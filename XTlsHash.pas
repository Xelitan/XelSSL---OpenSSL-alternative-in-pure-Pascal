// XTls - a compact TLS 1.2/1.3 client in pure Pascal.
// XTlsHash: SHA-1, SHA-256, SHA-384, SHA-512, HMAC, HKDF (RFC 5869),
// HKDF-Expand-Label (RFC 8446), TLS 1.2 PRF (RFC 5246).
//
// SHA-2 constants taken from HashLib4Pascal (Ugochukwu Mmaduekwe, MIT license).
// License: MIT.
unit XTlsHash;

{$mode objfpc}{$H+}{$Q-}{$R-}

interface

uses
  SysUtils;

type
  THashAlg = (haSHA1, haSHA256, haSHA384, haSHA512);

  // Hash state. The record can be copied - this is how the "current" transcript
  // hash is computed without finishing the original.
  TXHash = record
    Alg: THashAlg;
    H32: array[0..7] of UInt32;     // SHA-1 / SHA-256
    H64: array[0..7] of UInt64;     // SHA-384 / SHA-512
    Buf: array[0..127] of Byte;
    BufLen: Integer;
    Total: QWord;                   // number of bytes
  end;

function HashSize(Alg: THashAlg): Integer;
function HashBlockSize(Alg: THashAlg): Integer;
procedure HashInit(out C: TXHash; Alg: THashAlg);
procedure HashUpdate(var C: TXHash; P: PByte; Len: Integer); overload;
procedure HashUpdate(var C: TXHash; const Data: TBytes); overload;
function HashFinal(var C: TXHash): TBytes;
function HashPeek(const C: TXHash): TBytes;      // hash of the data so far, C unchanged
function Hash(Alg: THashAlg; const Data: TBytes): TBytes;

function Hmac(Alg: THashAlg; const Key, Data: TBytes): TBytes;
function HkdfExtract(Alg: THashAlg; const Salt, Ikm: TBytes): TBytes;
function HkdfExpand(Alg: THashAlg; const Prk, Info: TBytes; Len: Integer): TBytes;
function HkdfExpandLabel(Alg: THashAlg; const Secret: TBytes; const ALabel: string;
  const Context: TBytes; Len: Integer): TBytes;
function Tls12Prf(Alg: THashAlg; const Secret: TBytes; const ALabel: string;
  const Seed: TBytes; Len: Integer): TBytes;

// Byte helpers (used throughout XTls)
function BytesOf(const S: RawByteString): TBytes;
function Concat(const A, B: TBytes): TBytes; overload;
function Concat(const A, B, C: TBytes): TBytes; overload;
function SubBytes(const A: TBytes; Start, Len: Integer): TBytes;
function SameBytesCT(const A, B: TBytes): Boolean;   // constant-time comparison
function ToHex(const A: TBytes): string;
function FromHex(const S: string): TBytes;
procedure Wipe(var A: TBytes);

implementation

const
  K256: array[0..63] of UInt32 = (
    $428A2F98, $71374491, $B5C0FBCF, $E9B5DBA5, $3956C25B, $59F111F1, $923F82A4, $AB1C5ED5,
    $D807AA98, $12835B01, $243185BE, $550C7DC3, $72BE5D74, $80DEB1FE, $9BDC06A7, $C19BF174,
    $E49B69C1, $EFBE4786, $0FC19DC6, $240CA1CC, $2DE92C6F, $4A7484AA, $5CB0A9DC, $76F988DA,
    $983E5152, $A831C66D, $B00327C8, $BF597FC7, $C6E00BF3, $D5A79147, $06CA6351, $14292967,
    $27B70A85, $2E1B2138, $4D2C6DFC, $53380D13, $650A7354, $766A0ABB, $81C2C92E, $92722C85,
    $A2BFE8A1, $A81A664B, $C24B8B70, $C76C51A3, $D192E819, $D6990624, $F40E3585, $106AA070,
    $19A4C116, $1E376C08, $2748774C, $34B0BCB5, $391C0CB3, $4ED8AA4A, $5B9CCA4F, $682E6FF3,
    $748F82EE, $78A5636F, $84C87814, $8CC70208, $90BEFFFA, $A4506CEB, $BEF9A3F7, $C67178F2);

  K512: array[0..79] of UInt64 = (
    UInt64($428A2F98D728AE22), UInt64($7137449123EF65CD), UInt64($B5C0FBCFEC4D3B2F), UInt64($E9B5DBA58189DBBC),
    UInt64($3956C25BF348B538), UInt64($59F111F1B605D019), UInt64($923F82A4AF194F9B), UInt64($AB1C5ED5DA6D8118),
    UInt64($D807AA98A3030242), UInt64($12835B0145706FBE), UInt64($243185BE4EE4B28C), UInt64($550C7DC3D5FFB4E2),
    UInt64($72BE5D74F27B896F), UInt64($80DEB1FE3B1696B1), UInt64($9BDC06A725C71235), UInt64($C19BF174CF692694),
    UInt64($E49B69C19EF14AD2), UInt64($EFBE4786384F25E3), UInt64($0FC19DC68B8CD5B5), UInt64($240CA1CC77AC9C65),
    UInt64($2DE92C6F592B0275), UInt64($4A7484AA6EA6E483), UInt64($5CB0A9DCBD41FBD4), UInt64($76F988DA831153B5),
    UInt64($983E5152EE66DFAB), UInt64($A831C66D2DB43210), UInt64($B00327C898FB213F), UInt64($BF597FC7BEEF0EE4),
    UInt64($C6E00BF33DA88FC2), UInt64($D5A79147930AA725), UInt64($06CA6351E003826F), UInt64($142929670A0E6E70),
    UInt64($27B70A8546D22FFC), UInt64($2E1B21385C26C926), UInt64($4D2C6DFC5AC42AED), UInt64($53380D139D95B3DF),
    UInt64($650A73548BAF63DE), UInt64($766A0ABB3C77B2A8), UInt64($81C2C92E47EDAEE6), UInt64($92722C851482353B),
    UInt64($A2BFE8A14CF10364), UInt64($A81A664BBC423001), UInt64($C24B8B70D0F89791), UInt64($C76C51A30654BE30),
    UInt64($D192E819D6EF5218), UInt64($D69906245565A910), UInt64($F40E35855771202A), UInt64($106AA07032BBD1B8),
    UInt64($19A4C116B8D2D0C8), UInt64($1E376C085141AB53), UInt64($2748774CDF8EEB99), UInt64($34B0BCB5E19B48A8),
    UInt64($391C0CB3C5C95A63), UInt64($4ED8AA4AE3418ACB), UInt64($5B9CCA4F7763E373), UInt64($682E6FF3D6B2B8A3),
    UInt64($748F82EE5DEFB2FC), UInt64($78A5636F43172F60), UInt64($84C87814A1F0AB72), UInt64($8CC702081A6439EC),
    UInt64($90BEFFFA23631E28), UInt64($A4506CEBDE82BDE9), UInt64($BEF9A3F7B2C67915), UInt64($C67178F2E372532B),
    UInt64($CA273ECEEA26619C), UInt64($D186B8C721C0C207), UInt64($EADA7DD6CDE0EB1E), UInt64($F57D4F7FEE6ED178),
    UInt64($06F067AA72176FBA), UInt64($0A637DC5A2C898A6), UInt64($113F9804BEF90DAE), UInt64($1B710B35131C471B),
    UInt64($28DB77F523047D84), UInt64($32CAAB7B40C72493), UInt64($3C9EBE0A15C9BEBC), UInt64($431D67C49C100D4C),
    UInt64($4CC5D4BECB3E42B6), UInt64($597F299CFC657E2A), UInt64($5FCB6FAB3AD6FAEC), UInt64($6C44198C4A475817));

function Ror32(X: UInt32; N: Integer): UInt32; inline;
begin Result := (X shr N) or (X shl (32 - N)); end;

function Rol32(X: UInt32; N: Integer): UInt32; inline;
begin Result := (X shl N) or (X shr (32 - N)); end;

function Ror64(X: UInt64; N: Integer): UInt64; inline;
begin Result := (X shr N) or (X shl (64 - N)); end;

function BE32(P: PByte): UInt32; inline;
begin Result := (UInt32(P[0]) shl 24) or (UInt32(P[1]) shl 16) or (UInt32(P[2]) shl 8) or P[3]; end;

function BE64(P: PByte): UInt64; inline;
begin Result := (UInt64(BE32(P)) shl 32) or BE32(P + 4); end;

// ---- blocks ----

procedure Sha1Block(var C: TXHash; P: PByte);
var W: array[0..79] of UInt32; a, b, cc, d, e, t, f, k: UInt32; i: Integer;
begin
  for i := 0 to 15 do W[i] := BE32(P + i * 4);
  for i := 16 to 79 do W[i] := Rol32(W[i-3] xor W[i-8] xor W[i-14] xor W[i-16], 1);
  a := C.H32[0]; b := C.H32[1]; cc := C.H32[2]; d := C.H32[3]; e := C.H32[4];
  for i := 0 to 79 do
  begin
    if i < 20 then begin f := (b and cc) or ((not b) and d); k := $5A827999; end
    else if i < 40 then begin f := b xor cc xor d; k := $6ED9EBA1; end
    else if i < 60 then begin f := (b and cc) or (b and d) or (cc and d); k := $8F1BBCDC; end
    else begin f := b xor cc xor d; k := $CA62C1D6; end;
    t := Rol32(a, 5) + f + e + k + W[i];
    e := d; d := cc; cc := Rol32(b, 30); b := a; a := t;
  end;
  Inc(C.H32[0], a); Inc(C.H32[1], b); Inc(C.H32[2], cc); Inc(C.H32[3], d); Inc(C.H32[4], e);
end;

procedure Sha256Block(var C: TXHash; P: PByte);
var W: array[0..63] of UInt32; a, b, cc, d, e, f, g, h, t1, t2: UInt32; i: Integer;
begin
  for i := 0 to 15 do W[i] := BE32(P + i * 4);
  for i := 16 to 63 do
    W[i] := (Ror32(W[i-2], 17) xor Ror32(W[i-2], 19) xor (W[i-2] shr 10)) + W[i-7] +
            (Ror32(W[i-15], 7) xor Ror32(W[i-15], 18) xor (W[i-15] shr 3)) + W[i-16];
  a := C.H32[0]; b := C.H32[1]; cc := C.H32[2]; d := C.H32[3];
  e := C.H32[4]; f := C.H32[5]; g := C.H32[6]; h := C.H32[7];
  for i := 0 to 63 do
  begin
    t1 := h + (Ror32(e, 6) xor Ror32(e, 11) xor Ror32(e, 25)) + ((e and f) xor ((not e) and g)) + K256[i] + W[i];
    t2 := (Ror32(a, 2) xor Ror32(a, 13) xor Ror32(a, 22)) + ((a and b) xor (a and cc) xor (b and cc));
    h := g; g := f; f := e; e := d + t1; d := cc; cc := b; b := a; a := t1 + t2;
  end;
  Inc(C.H32[0], a); Inc(C.H32[1], b); Inc(C.H32[2], cc); Inc(C.H32[3], d);
  Inc(C.H32[4], e); Inc(C.H32[5], f); Inc(C.H32[6], g); Inc(C.H32[7], h);
end;

procedure Sha512Block(var C: TXHash; P: PByte);
var W: array[0..79] of UInt64; a, b, cc, d, e, f, g, h, t1, t2: UInt64; i: Integer;
begin
  for i := 0 to 15 do W[i] := BE64(P + i * 8);
  for i := 16 to 79 do
    W[i] := (Ror64(W[i-2], 19) xor Ror64(W[i-2], 61) xor (W[i-2] shr 6)) + W[i-7] +
            (Ror64(W[i-15], 1) xor Ror64(W[i-15], 8) xor (W[i-15] shr 7)) + W[i-16];
  a := C.H64[0]; b := C.H64[1]; cc := C.H64[2]; d := C.H64[3];
  e := C.H64[4]; f := C.H64[5]; g := C.H64[6]; h := C.H64[7];
  for i := 0 to 79 do
  begin
    t1 := h + (Ror64(e, 14) xor Ror64(e, 18) xor Ror64(e, 41)) + ((e and f) xor ((not e) and g)) + K512[i] + W[i];
    t2 := (Ror64(a, 28) xor Ror64(a, 34) xor Ror64(a, 39)) + ((a and b) xor (a and cc) xor (b and cc));
    h := g; g := f; f := e; e := d + t1; d := cc; cc := b; b := a; a := t1 + t2;
  end;
  Inc(C.H64[0], a); Inc(C.H64[1], b); Inc(C.H64[2], cc); Inc(C.H64[3], d);
  Inc(C.H64[4], e); Inc(C.H64[5], f); Inc(C.H64[6], g); Inc(C.H64[7], h);
end;

procedure Block(var C: TXHash; P: PByte); inline;
begin
  case C.Alg of
    haSHA1: Sha1Block(C, P);
    haSHA256: Sha256Block(C, P);
  else Sha512Block(C, P);
  end;
end;

// ---- hash API ----

function HashSize(Alg: THashAlg): Integer;
const S: array[THashAlg] of Integer = (20, 32, 48, 64);
begin Result := S[Alg]; end;

function HashBlockSize(Alg: THashAlg): Integer;
begin if Alg in [haSHA1, haSHA256] then Result := 64 else Result := 128; end;

procedure HashInit(out C: TXHash; Alg: THashAlg);
begin
  FillChar(C, SizeOf(C), 0);
  C.Alg := Alg;
  case Alg of
    haSHA1:
      begin
        C.H32[0] := $67452301; C.H32[1] := $EFCDAB89; C.H32[2] := $98BADCFE;
        C.H32[3] := $10325476; C.H32[4] := $C3D2E1F0;
      end;
    haSHA256:
      begin
        C.H32[0] := $6A09E667; C.H32[1] := $BB67AE85; C.H32[2] := $3C6EF372; C.H32[3] := $A54FF53A;
        C.H32[4] := $510E527F; C.H32[5] := $9B05688C; C.H32[6] := $1F83D9AB; C.H32[7] := $5BE0CD19;
      end;
    haSHA384:
      begin
        C.H64[0] := UInt64($CBBB9D5DC1059ED8); C.H64[1] := UInt64($629A292A367CD507);
        C.H64[2] := UInt64($9159015A3070DD17); C.H64[3] := UInt64($152FECD8F70E5939);
        C.H64[4] := UInt64($67332667FFC00B31); C.H64[5] := UInt64($8EB44A8768581511);
        C.H64[6] := UInt64($DB0C2E0D64F98FA7); C.H64[7] := UInt64($47B5481DBEFA4FA4);
      end;
    haSHA512:
      begin
        C.H64[0] := UInt64($6A09E667F3BCC908); C.H64[1] := UInt64($BB67AE8584CAA73B);
        C.H64[2] := UInt64($3C6EF372FE94F82B); C.H64[3] := UInt64($A54FF53A5F1D36F1);
        C.H64[4] := UInt64($510E527FADE682D1); C.H64[5] := UInt64($9B05688C2B3E6C1F);
        C.H64[6] := UInt64($1F83D9ABFB41BD6B); C.H64[7] := UInt64($5BE0CD19137E2179);
      end;
  end;
end;

procedure HashUpdate(var C: TXHash; P: PByte; Len: Integer);
var bs, n: Integer;
begin
  if Len <= 0 then Exit;
  bs := HashBlockSize(C.Alg);
  Inc(C.Total, Len);
  if C.BufLen > 0 then
  begin
    n := bs - C.BufLen;
    if n > Len then n := Len;
    Move(P^, C.Buf[C.BufLen], n);
    Inc(C.BufLen, n); Inc(P, n); Dec(Len, n);
    if C.BufLen = bs then begin Block(C, @C.Buf[0]); C.BufLen := 0; end;
  end;
  while Len >= bs do
  begin
    Block(C, P);
    Inc(P, bs); Dec(Len, bs);
  end;
  if Len > 0 then begin Move(P^, C.Buf[0], Len); C.BufLen := Len; end;
end;

procedure HashUpdate(var C: TXHash; const Data: TBytes);
begin
  if Length(Data) > 0 then HashUpdate(C, @Data[0], Length(Data));
end;

function HashFinal(var C: TXHash): TBytes;
var bs, lenOff, i: Integer; bits: QWord;
begin
  bs := HashBlockSize(C.Alg);
  lenOff := bs - 8;                      // bit length in the last 8 bytes (SHA-384/512: 16, upper half = 0)
  bits := C.Total * 8;
  C.Buf[C.BufLen] := $80; Inc(C.BufLen);
  if C.BufLen > lenOff - (bs div 64 - 1) * 8 then
  begin
    FillChar(C.Buf[C.BufLen], bs - C.BufLen, 0);
    Block(C, @C.Buf[0]);
    C.BufLen := 0;
  end;
  FillChar(C.Buf[C.BufLen], bs - C.BufLen, 0);
  for i := 0 to 7 do C.Buf[bs - 1 - i] := Byte(bits shr (8 * i));
  Block(C, @C.Buf[0]);
  SetLength(Result, HashSize(C.Alg));
  if C.Alg in [haSHA1, haSHA256] then
    for i := 0 to HashSize(C.Alg) - 1 do Result[i] := Byte(C.H32[i shr 2] shr (24 - 8 * (i and 3)))
  else
    for i := 0 to HashSize(C.Alg) - 1 do Result[i] := Byte(C.H64[i shr 3] shr (56 - 8 * (i and 7)));
  FillChar(C, SizeOf(C), 0);
end;

function HashPeek(const C: TXHash): TBytes;
var T: TXHash;
begin
  T := C;
  Result := HashFinal(T);
end;

function Hash(Alg: THashAlg; const Data: TBytes): TBytes;
var C: TXHash;
begin
  HashInit(C, Alg);
  HashUpdate(C, Data);
  Result := HashFinal(C);
end;

// ---- HMAC / HKDF / PRF ----

function Hmac(Alg: THashAlg; const Key, Data: TBytes): TBytes;
var bs, i: Integer; k, ipad, opad: TBytes; C: TXHash;
begin
  bs := HashBlockSize(Alg);
  if Length(Key) > bs then k := Hash(Alg, Key) else k := Copy(Key);
  SetLength(k, bs);                      // pad with zeros
  SetLength(ipad, bs); SetLength(opad, bs);
  for i := 0 to bs - 1 do begin ipad[i] := k[i] xor $36; opad[i] := k[i] xor $5C; end;
  HashInit(C, Alg); HashUpdate(C, ipad); HashUpdate(C, Data);
  Result := HashFinal(C);
  HashInit(C, Alg); HashUpdate(C, opad); HashUpdate(C, Result);
  Result := HashFinal(C);
  Wipe(k); Wipe(ipad); Wipe(opad);
end;

function HkdfExtract(Alg: THashAlg; const Salt, Ikm: TBytes): TBytes;
var s: TBytes;
begin
  if Length(Salt) = 0 then SetLength(s, HashSize(Alg)) else s := Salt;   // no salt = zeros
  Result := Hmac(Alg, s, Ikm);
end;

function HkdfExpand(Alg: THashAlg; const Prk, Info: TBytes; Len: Integer): TBytes;
var t, blk: TBytes; n, off: Integer;
begin
  SetLength(Result, Len);
  t := nil; off := 0; n := 1;
  while off < Len do
  begin
    blk := Concat(t, Info, TBytes.Create(Byte(n)));
    t := Hmac(Alg, Prk, blk);
    if Len - off < Length(t) then Move(t[0], Result[off], Len - off)
    else Move(t[0], Result[off], Length(t));
    Inc(off, Length(t)); Inc(n);
  end;
end;

function HkdfExpandLabel(Alg: THashAlg; const Secret: TBytes; const ALabel: string;
  const Context: TBytes; Len: Integer): TBytes;
var info, lab: TBytes;
begin
  lab := BytesOf('tls13 ' + ALabel);
  info := Concat(TBytes.Create(Byte(Len shr 8), Byte(Len), Byte(Length(lab))), lab,
                 Concat(TBytes.Create(Byte(Length(Context))), Context));
  Result := HkdfExpand(Alg, Secret, info, Len);
end;

function Tls12Prf(Alg: THashAlg; const Secret: TBytes; const ALabel: string;
  const Seed: TBytes; Len: Integer): TBytes;
var s, a, p: TBytes; off: Integer;
begin
  // P_hash(secret, label + seed): A(1) = HMAC(secret, seed), output = HMAC(A(i) + seed) ...
  s := Concat(BytesOf(ALabel), Seed);
  SetLength(Result, Len);
  a := Hmac(Alg, Secret, s);
  off := 0;
  while off < Len do
  begin
    p := Hmac(Alg, Secret, Concat(a, s));
    if Len - off < Length(p) then Move(p[0], Result[off], Len - off)
    else Move(p[0], Result[off], Length(p));
    Inc(off, Length(p));
    a := Hmac(Alg, Secret, a);
  end;
end;

// ---- bytes ----

function BytesOf(const S: RawByteString): TBytes;
begin
  SetLength(Result, Length(S));
  if Length(S) > 0 then Move(S[1], Result[0], Length(S));
end;

function Concat(const A, B: TBytes): TBytes;
begin
  SetLength(Result, Length(A) + Length(B));
  if Length(A) > 0 then Move(A[0], Result[0], Length(A));
  if Length(B) > 0 then Move(B[0], Result[Length(A)], Length(B));
end;

function Concat(const A, B, C: TBytes): TBytes;
begin
  Result := Concat(Concat(A, B), C);
end;

function SubBytes(const A: TBytes; Start, Len: Integer): TBytes;
begin
  if (Start < 0) or (Len < 0) or (Start + Len > Length(A)) then
    raise ERangeError.Create('XTls: SubBytes out of range');
  SetLength(Result, Len);
  if Len > 0 then Move(A[Start], Result[0], Len);
end;

function SameBytesCT(const A, B: TBytes): Boolean;
var i: Integer; d: Byte;
begin
  if Length(A) <> Length(B) then Exit(False);
  d := 0;
  for i := 0 to High(A) do d := d or (A[i] xor B[i]);
  Result := d = 0;
end;

function ToHex(const A: TBytes): string;
const HX = '0123456789abcdef';
var i: Integer;
begin
  SetLength(Result, Length(A) * 2);
  for i := 0 to High(A) do
  begin
    Result[i * 2 + 1] := HX[(A[i] shr 4) + 1];
    Result[i * 2 + 2] := HX[(A[i] and 15) + 1];
  end;
end;

function FromHex(const S: string): TBytes;
var i, n: Integer; t: string;
begin
  t := '';
  for i := 1 to Length(S) do
    if S[i] in ['0'..'9', 'a'..'f', 'A'..'F'] then t := t + S[i];
  n := Length(t) div 2;
  SetLength(Result, n);
  for i := 0 to n - 1 do Result[i] := StrToInt('$' + Copy(t, i * 2 + 1, 2));
end;

procedure Wipe(var A: TBytes);
begin
  if Length(A) > 0 then FillChar(A[0], Length(A), 0);
  A := nil;
end;

end.
