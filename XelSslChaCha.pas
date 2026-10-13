// XelSSL - ChaCha20-Poly1305 AEAD (RFC 8439).
// Poly1305 in the 26-bit variant (poly1305-donna, A. Moon) - no data-dependent
// branches. License: MIT.
unit XelSslChaCha;

{$mode objfpc}{$H+}{$Q-}{$R-}

interface

uses
  SysUtils;

// Returns ciphertext || tag (16 bytes). Key = 32 bytes, Nonce = 12 bytes.
function ChaChaPolySeal(const Key, Nonce, AAD, Plain: TBytes): TBytes;
function ChaChaPolyOpen(const Key, Nonce, AAD, Data: TBytes; out Plain: TBytes): Boolean;

// Exported for tests
procedure ChaCha20Xor(const Key, Nonce: TBytes; Counter: UInt32; Src, Dst: PByte; Len: Integer);
function Poly1305Mac(const Key32: TBytes; const Msg: TBytes): TBytes;

implementation

uses XelSslHash;

function Rol(X: UInt32; N: Integer): UInt32; inline;
begin Result := (X shl N) or (X shr (32 - N)); end;

function LE32(P: PByte): UInt32; inline;
begin Result := P[0] or (UInt32(P[1]) shl 8) or (UInt32(P[2]) shl 16) or (UInt32(P[3]) shl 24); end;

procedure ChaChaBlock(const Inp: array of UInt32; out Outp: array of Byte);
var x: array[0..15] of UInt32; i: Integer;
  procedure QR(a, b, c, d: Integer);
  begin
    x[a] := x[a] + x[b]; x[d] := Rol(x[d] xor x[a], 16);
    x[c] := x[c] + x[d]; x[b] := Rol(x[b] xor x[c], 12);
    x[a] := x[a] + x[b]; x[d] := Rol(x[d] xor x[a], 8);
    x[c] := x[c] + x[d]; x[b] := Rol(x[b] xor x[c], 7);
  end;
begin
  for i := 0 to 15 do x[i] := Inp[i];
  for i := 1 to 10 do
  begin
    QR(0, 4, 8, 12); QR(1, 5, 9, 13); QR(2, 6, 10, 14); QR(3, 7, 11, 15);
    QR(0, 5, 10, 15); QR(1, 6, 11, 12); QR(2, 7, 8, 13); QR(3, 4, 9, 14);
  end;
  for i := 0 to 15 do
  begin
    x[i] := x[i] + Inp[i];
    Outp[i * 4] := Byte(x[i]); Outp[i * 4 + 1] := Byte(x[i] shr 8);
    Outp[i * 4 + 2] := Byte(x[i] shr 16); Outp[i * 4 + 3] := Byte(x[i] shr 24);
  end;
end;

procedure ChaCha20Xor(const Key, Nonce: TBytes; Counter: UInt32; Src, Dst: PByte; Len: Integer);
var st: array[0..15] of UInt32; ks: array[0..63] of Byte; i, n: Integer;
begin
  st[0] := $61707865; st[1] := $3320646E; st[2] := $79622D32; st[3] := $6B206574;
  for i := 0 to 7 do st[4 + i] := LE32(@Key[i * 4]);
  st[12] := Counter;
  for i := 0 to 2 do st[13 + i] := LE32(@Nonce[i * 4]);
  while Len > 0 do
  begin
    ChaChaBlock(st, ks);
    n := 64; if n > Len then n := Len;
    for i := 0 to n - 1 do Dst[i] := Src[i] xor ks[i];
    Inc(Src, n); Inc(Dst, n); Dec(Len, n);
    st[12] := st[12] + 1;
  end;
  FillChar(ks, SizeOf(ks), 0); FillChar(st, SizeOf(st), 0);
end;

// ---- Poly1305 (26-bit limbs) ----

type
  TPoly = record
    r, h, pad: array[0..4] of UInt32;
    s: array[0..3] of UInt32;
  end;

procedure PolyInit(out P: TPoly; const Key: TBytes);
begin
  FillChar(P, SizeOf(P), 0);
  // r &= 0ffffffc0ffffffc0ffffffc0fffffff
  P.r[0] := (LE32(@Key[0])) and $3FFFFFF;
  P.r[1] := (LE32(@Key[3]) shr 2) and $3FFFF03;
  P.r[2] := (LE32(@Key[6]) shr 4) and $3FFC0FF;
  P.r[3] := (LE32(@Key[9]) shr 6) and $3F03FFF;
  P.r[4] := (LE32(@Key[12]) shr 8) and $00FFFFF;
  P.s[0] := LE32(@Key[16]); P.s[1] := LE32(@Key[20]);
  P.s[2] := LE32(@Key[24]); P.s[3] := LE32(@Key[28]);
end;

// one 16-byte block; HiBit = 1 shl 24 for full blocks (bit 2^128), 0 for the padded last one
procedure PolyBlock(var P: TPoly; M: PByte; HiBit: UInt32);
var r0, r1, r2, r3, r4, s1, s2, s3, s4, h0, h1, h2, h3, h4, c: UInt32;
    d0, d1, d2, d3, d4: UInt64;
begin
  r0 := P.r[0]; r1 := P.r[1]; r2 := P.r[2]; r3 := P.r[3]; r4 := P.r[4];
  s1 := r1 * 5; s2 := r2 * 5; s3 := r3 * 5; s4 := r4 * 5;
  h0 := P.h[0]; h1 := P.h[1]; h2 := P.h[2]; h3 := P.h[3]; h4 := P.h[4];
  h0 := h0 + (LE32(M) and $3FFFFFF);
  h1 := h1 + ((LE32(M + 3) shr 2) and $3FFFFFF);
  h2 := h2 + ((LE32(M + 6) shr 4) and $3FFFFFF);
  h3 := h3 + ((LE32(M + 9) shr 6) and $3FFFFFF);
  h4 := h4 + ((LE32(M + 12) shr 8) or HiBit);
  d0 := UInt64(h0) * r0 + UInt64(h1) * s4 + UInt64(h2) * s3 + UInt64(h3) * s2 + UInt64(h4) * s1;
  d1 := UInt64(h0) * r1 + UInt64(h1) * r0 + UInt64(h2) * s4 + UInt64(h3) * s3 + UInt64(h4) * s2;
  d2 := UInt64(h0) * r2 + UInt64(h1) * r1 + UInt64(h2) * r0 + UInt64(h3) * s4 + UInt64(h4) * s3;
  d3 := UInt64(h0) * r3 + UInt64(h1) * r2 + UInt64(h2) * r1 + UInt64(h3) * r0 + UInt64(h4) * s4;
  d4 := UInt64(h0) * r4 + UInt64(h1) * r3 + UInt64(h2) * r2 + UInt64(h3) * r1 + UInt64(h4) * r0;
  c := UInt32(d0 shr 26); h0 := UInt32(d0) and $3FFFFFF;
  d1 := d1 + c; c := UInt32(d1 shr 26); h1 := UInt32(d1) and $3FFFFFF;
  d2 := d2 + c; c := UInt32(d2 shr 26); h2 := UInt32(d2) and $3FFFFFF;
  d3 := d3 + c; c := UInt32(d3 shr 26); h3 := UInt32(d3) and $3FFFFFF;
  d4 := d4 + c; c := UInt32(d4 shr 26); h4 := UInt32(d4) and $3FFFFFF;
  h0 := h0 + c * 5; c := h0 shr 26; h0 := h0 and $3FFFFFF;
  h1 := h1 + c;
  P.h[0] := h0; P.h[1] := h1; P.h[2] := h2; P.h[3] := h3; P.h[4] := h4;
end;

procedure PolyUpdate(var P: TPoly; const Data: TBytes; PadTo16: Boolean);
var i, n, r: Integer; blk: array[0..15] of Byte;
begin
  n := Length(Data) div 16;
  for i := 0 to n - 1 do PolyBlock(P, @Data[i * 16], 1 shl 24);
  r := Length(Data) - n * 16;
  if r > 0 then
  begin
    FillChar(blk, 16, 0);
    Move(Data[n * 16], blk[0], r);
    if PadTo16 then
      PolyBlock(P, @blk[0], 1 shl 24)         // AEAD: zero padding to 16 bytes, full block
    else
    begin
      blk[r] := 1;                             // plain Poly1305: a 1 bit after the data
      PolyBlock(P, @blk[0], 0);
    end;
  end;
end;

function PolyFinish(var P: TPoly): TBytes;
var h0, h1, h2, h3, h4, c, g0, g1, g2, g3, g4, mask: UInt32; f: UInt64;
begin
  h0 := P.h[0]; h1 := P.h[1]; h2 := P.h[2]; h3 := P.h[3]; h4 := P.h[4];
  c := h1 shr 26; h1 := h1 and $3FFFFFF;
  h2 := h2 + c; c := h2 shr 26; h2 := h2 and $3FFFFFF;
  h3 := h3 + c; c := h3 shr 26; h3 := h3 and $3FFFFFF;
  h4 := h4 + c; c := h4 shr 26; h4 := h4 and $3FFFFFF;
  h0 := h0 + c * 5; c := h0 shr 26; h0 := h0 and $3FFFFFF;
  h1 := h1 + c;
  // g = h + -p
  g0 := h0 + 5; c := g0 shr 26; g0 := g0 and $3FFFFFF;
  g1 := h1 + c; c := g1 shr 26; g1 := g1 and $3FFFFFF;
  g2 := h2 + c; c := g2 shr 26; g2 := g2 and $3FFFFFF;
  g3 := h3 + c; c := g3 shr 26; g3 := g3 and $3FFFFFF;
  g4 := h4 + c - (1 shl 26);
  // select h if h < p, otherwise g (branch-free)
  mask := (g4 shr 31) - 1;
  g0 := g0 and mask; g1 := g1 and mask; g2 := g2 and mask; g3 := g3 and mask; g4 := g4 and mask;
  mask := not mask;
  h0 := (h0 and mask) or g0; h1 := (h1 and mask) or g1; h2 := (h2 and mask) or g2;
  h3 := (h3 and mask) or g3; h4 := (h4 and mask) or g4;
  // h = h % 2^128
  h0 := (h0 or (h1 shl 26));
  h1 := ((h1 shr 6) or (h2 shl 20));
  h2 := ((h2 shr 12) or (h3 shl 14));
  h3 := ((h3 shr 18) or (h4 shl 8));
  // tag = h + s
  f := UInt64(h0) + P.s[0]; h0 := UInt32(f);
  f := UInt64(h1) + P.s[1] + (f shr 32); h1 := UInt32(f);
  f := UInt64(h2) + P.s[2] + (f shr 32); h2 := UInt32(f);
  f := UInt64(h3) + P.s[3] + (f shr 32); h3 := UInt32(f);
  SetLength(Result, 16);
  Move(h0, Result[0], 4); Move(h1, Result[4], 4); Move(h2, Result[8], 4); Move(h3, Result[12], 4);
  {$IFDEF ENDIAN_BIG}{$ERROR XelSSL Poly1305: wymaga little-endian}{$ENDIF}
  FillChar(P, SizeOf(P), 0);
end;

function Poly1305Mac(const Key32: TBytes; const Msg: TBytes): TBytes;
var P: TPoly;
begin
  PolyInit(P, Key32);
  PolyUpdate(P, Msg, False);
  Result := PolyFinish(P);
end;

function AeadTag(const OtkKey, AAD, Cipher: TBytes): TBytes;
var P: TPoly; lens: TBytes; i: Integer; a, c: QWord;
begin
  PolyInit(P, OtkKey);
  PolyUpdate(P, AAD, True);
  PolyUpdate(P, Cipher, True);
  SetLength(lens, 16);
  a := Length(AAD); c := Length(Cipher);
  for i := 0 to 7 do begin lens[i] := Byte(a shr (8 * i)); lens[8 + i] := Byte(c shr (8 * i)); end;
  PolyUpdate(P, lens, True);
  Result := PolyFinish(P);
end;

function OneTimeKey(const Key, Nonce: TBytes): TBytes;
var z: TBytes;
begin
  SetLength(z, 32); FillChar(z[0], 32, 0);
  SetLength(Result, 32);
  ChaCha20Xor(Key, Nonce, 0, @z[0], @Result[0], 32);
end;

function ChaChaPolySeal(const Key, Nonce, AAD, Plain: TBytes): TBytes;
var c, otk: TBytes;
begin
  if (Length(Key) <> 32) or (Length(Nonce) <> 12) then raise Exception.Create('XelSSL ChaCha20: invalid key/nonce');
  SetLength(c, Length(Plain));
  if Length(Plain) > 0 then ChaCha20Xor(Key, Nonce, 1, @Plain[0], @c[0], Length(Plain));
  otk := OneTimeKey(Key, Nonce);
  Result := Concat(c, AeadTag(otk, AAD, c));
  Wipe(otk);
end;

function ChaChaPolyOpen(const Key, Nonce, AAD, Data: TBytes; out Plain: TBytes): Boolean;
var c, otk, tag: TBytes;
begin
  Plain := nil;
  if (Length(Key) <> 32) or (Length(Nonce) <> 12) or (Length(Data) < 16) then Exit(False);
  c := Copy(Data, 0, Length(Data) - 16);
  otk := OneTimeKey(Key, Nonce);
  tag := AeadTag(otk, AAD, c);
  Wipe(otk);
  if not SameBytesCT(tag, Copy(Data, Length(Data) - 16, 16)) then Exit(False);
  SetLength(Plain, Length(c));
  if Length(c) > 0 then ChaCha20Xor(Key, Nonce, 1, @c[0], @Plain[0], Length(c));
  Result := True;
end;

end.
