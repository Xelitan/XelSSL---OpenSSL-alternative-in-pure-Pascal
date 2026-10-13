// XelSSL - AES (128/256, encryption only) + AES-GCM (RFC 5288 / RFC 8446).
//
// AES: bitsliced, no data- or key-dependent table lookups (constant time) - a port of
// aes_ct64 (BearSSL, Thomas Pornin) via CryptoLib4Pascal TAesBitSlicedEngine
// (Ugochukwu Mmaduekwe, MIT). GHASH: table-free multiplication in GF(2^128) (ImplMul64
// from CryptoLib4Pascal TGcmUtilities, MIT). GCM only needs AES encryption.
// License: MIT.
unit XelSslAes;

{$mode objfpc}{$H+}{$Q-}{$R-}

interface

uses
  SysUtils;

type
  TAesKey = record
    Rounds: Integer;
    SK: array[0..119] of UInt64;           // (Rounds+1)*8 bitsliced words
  end;

  PGcmKey = ^TGcmKey;
  TGcmKey = record
    Aes: TAesKey;
    H0, H1: UInt64;                         // H = AES_K(0^128) as a field element
  end;

procedure AesSetKey(out K: TAesKey; const Key: TBytes);
// Encrypts N consecutive 16-byte blocks (Src and Dst identical or disjoint).
procedure AesEncryptBlocks(const K: TAesKey; Src, Dst: PByte; N: Integer);

procedure GcmSetKey(out G: TGcmKey; const Key: TBytes);
// Returns ciphertext || tag (16 bytes). Nonce = 12 bytes.
function GcmSeal(const G: TGcmKey; const Nonce, AAD, Plain: TBytes): TBytes;
// Data = ciphertext || tag. False if the tag does not match (Plain = nil).
function GcmOpen(const G: TGcmKey; const Nonce, AAD, Data: TBytes; out Plain: TBytes): Boolean;

implementation

uses XelSslHash;

type
  TBS = array[0..7] of UInt64;

const
  RCon: array[0..9] of Byte = ($01, $02, $04, $08, $10, $20, $40, $80, $1B, $36);

function Ror64(X: UInt64; N: Integer): UInt64; inline;
begin Result := (X shr N) or (X shl (64 - N)); end;

function LE32(P: PByte): UInt32; inline;
begin Result := P[0] or (UInt32(P[1]) shl 8) or (UInt32(P[2]) shl 16) or (UInt32(P[3]) shl 24); end;

procedure PutLE32(P: PByte; V: UInt32); inline;
begin P[0] := Byte(V); P[1] := Byte(V shr 8); P[2] := Byte(V shr 16); P[3] := Byte(V shr 24); end;

procedure Swapn(Cl, Ch: UInt64; S: Integer; var X, Y: UInt64); inline;
var a, b: UInt64;
begin
  a := X; b := Y;
  X := (a and Cl) or ((b and Cl) shl S);
  Y := ((a and Ch) shr S) or (b and Ch);
end;

procedure Ortho(var Q: TBS);
const
  CL2 = UInt64($5555555555555555); CH2 = UInt64($AAAAAAAAAAAAAAAA);
  CL4 = UInt64($3333333333333333); CH4 = UInt64($CCCCCCCCCCCCCCCC);
  CL8 = UInt64($0F0F0F0F0F0F0F0F); CH8 = UInt64($F0F0F0F0F0F0F0F0);
begin
  Swapn(CL2, CH2, 1, Q[0], Q[1]); Swapn(CL2, CH2, 1, Q[2], Q[3]);
  Swapn(CL2, CH2, 1, Q[4], Q[5]); Swapn(CL2, CH2, 1, Q[6], Q[7]);
  Swapn(CL4, CH4, 2, Q[0], Q[2]); Swapn(CL4, CH4, 2, Q[1], Q[3]);
  Swapn(CL4, CH4, 2, Q[4], Q[6]); Swapn(CL4, CH4, 2, Q[5], Q[7]);
  Swapn(CL8, CH8, 4, Q[0], Q[4]); Swapn(CL8, CH8, 4, Q[1], Q[5]);
  Swapn(CL8, CH8, 4, Q[2], Q[6]); Swapn(CL8, CH8, 4, Q[3], Q[7]);
end;

procedure InterleaveIn(W0, W1, W2, W3: UInt32; out Q0, Q1: UInt64);
const M16 = UInt64($0000FFFF0000FFFF); M8 = UInt64($00FF00FF00FF00FF);
var x0, x1, x2, x3: UInt64;
begin
  x0 := W0; x1 := W1; x2 := W2; x3 := W3;
  x0 := (x0 or (x0 shl 16)) and M16; x1 := (x1 or (x1 shl 16)) and M16;
  x2 := (x2 or (x2 shl 16)) and M16; x3 := (x3 or (x3 shl 16)) and M16;
  x0 := (x0 or (x0 shl 8)) and M8; x1 := (x1 or (x1 shl 8)) and M8;
  x2 := (x2 or (x2 shl 8)) and M8; x3 := (x3 or (x3 shl 8)) and M8;
  Q0 := x0 or (x2 shl 8);
  Q1 := x1 or (x3 shl 8);
end;

procedure InterleaveOut(out W0, W1, W2, W3: UInt32; Q0, Q1: UInt64);
const M16 = UInt64($0000FFFF0000FFFF); M8 = UInt64($00FF00FF00FF00FF);
var x0, x1, x2, x3: UInt64;
begin
  x0 := Q0 and M8; x1 := Q1 and M8;
  x2 := (Q0 shr 8) and M8; x3 := (Q1 shr 8) and M8;
  x0 := (x0 or (x0 shr 8)) and M16; x1 := (x1 or (x1 shr 8)) and M16;
  x2 := (x2 or (x2 shr 8)) and M16; x3 := (x3 or (x3 shr 8)) and M16;
  W0 := UInt32(x0) or UInt32(x0 shr 16); W1 := UInt32(x1) or UInt32(x1 shr 16);
  W2 := UInt32(x2) or UInt32(x2 shr 16); W3 := UInt32(x3) or UInt32(x3 shr 16);
end;

// S-box as a Boolean circuit (Boyar-Peralta) over 8 bit planes
procedure Sbox(var Q: TBS);
var
  x0, x1, x2, x3, x4, x5, x6, x7: UInt64;
  y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21: UInt64;
  z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17: UInt64;
  t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19: UInt64;
  t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37: UInt64;
  t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55: UInt64;
  t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67: UInt64;
  s0, s1, s2, s3, s4, s5, s6, s7: UInt64;
begin
  x0 := Q[7]; x1 := Q[6]; x2 := Q[5]; x3 := Q[4]; x4 := Q[3]; x5 := Q[2]; x6 := Q[1]; x7 := Q[0];
  y14 := x3 xor x5; y13 := x0 xor x6; y9 := x0 xor x3; y8 := x0 xor x5; t0 := x1 xor x2;
  y1 := t0 xor x7; y4 := y1 xor x3; y12 := y13 xor y14; y2 := y1 xor x0; y5 := y1 xor x6;
  y3 := y5 xor y8; t1 := x4 xor y12; y15 := t1 xor x5; y20 := t1 xor x1; y6 := y15 xor x7;
  y10 := y15 xor t0; y11 := y20 xor y9; y7 := x7 xor y11; y17 := y10 xor y11; y19 := y10 xor y8;
  y16 := t0 xor y11; y21 := y13 xor y16; y18 := x0 xor y16;

  t2 := y12 and y15; t3 := y3 and y6; t4 := t3 xor t2; t5 := y4 and x7; t6 := t5 xor t2;
  t7 := y13 and y16; t8 := y5 and y1; t9 := t8 xor t7; t10 := y2 and y7; t11 := t10 xor t7;
  t12 := y9 and y11; t13 := y14 and y17; t14 := t13 xor t12; t15 := y8 and y10; t16 := t15 xor t12;
  t17 := t4 xor t14; t18 := t6 xor t16; t19 := t9 xor t14; t20 := t11 xor t16;
  t21 := t17 xor y20; t22 := t18 xor y19; t23 := t19 xor y21; t24 := t20 xor y18;
  t25 := t21 xor t22; t26 := t21 and t23; t27 := t24 xor t26; t28 := t25 and t27; t29 := t28 xor t22;
  t30 := t23 xor t24; t31 := t22 xor t26; t32 := t31 and t30; t33 := t32 xor t24; t34 := t23 xor t33;
  t35 := t27 xor t33; t36 := t24 and t35; t37 := t36 xor t34; t38 := t27 xor t36; t39 := t29 and t38;
  t40 := t25 xor t39;
  t41 := t40 xor t37; t42 := t29 xor t33; t43 := t29 xor t40; t44 := t33 xor t37; t45 := t42 xor t41;
  z0 := t44 and y15; z1 := t37 and y6; z2 := t33 and x7; z3 := t43 and y16; z4 := t40 and y1;
  z5 := t29 and y7; z6 := t42 and y11; z7 := t45 and y17; z8 := t41 and y10; z9 := t44 and y12;
  z10 := t37 and y3; z11 := t33 and y4; z12 := t43 and y13; z13 := t40 and y5; z14 := t29 and y2;
  z15 := t42 and y9; z16 := t45 and y14; z17 := t41 and y8;

  t46 := z15 xor z16; t47 := z10 xor z11; t48 := z5 xor z13; t49 := z9 xor z10; t50 := z2 xor z12;
  t51 := z2 xor z5; t52 := z7 xor z8; t53 := z0 xor z3; t54 := z6 xor z7; t55 := z16 xor z17;
  t56 := z12 xor t48; t57 := t50 xor t53; t58 := z4 xor t46; t59 := z3 xor t54; t60 := t46 xor t57;
  t61 := z14 xor t57; t62 := t52 xor t58; t63 := t49 xor t58; t64 := z4 xor t59; t65 := t61 xor t62;
  t66 := z1 xor t63; s0 := t59 xor t63; s6 := t56 xor (not t62); s7 := t48 xor (not t60);
  t67 := t64 xor t65; s3 := t53 xor t66; s4 := t51 xor t66; s5 := t47 xor t65;
  s1 := t64 xor (not s3); s2 := t55 xor (not t67);
  Q[7] := s0; Q[6] := s1; Q[5] := s2; Q[4] := s3; Q[3] := s4; Q[2] := s5; Q[1] := s6; Q[0] := s7;
end;

procedure ShiftRows(var Q: TBS);
var i: Integer; x: UInt64;
begin
  for i := 0 to 7 do
  begin
    x := Q[i];
    Q[i] := (x and UInt64($000000000000FFFF))
      or ((x and UInt64($00000000FFF00000)) shr 4) or ((x and UInt64($00000000000F0000)) shl 12)
      or ((x and UInt64($0000FF0000000000)) shr 8) or ((x and UInt64($000000FF00000000)) shl 8)
      or ((x and UInt64($F000000000000000)) shr 12) or ((x and UInt64($0FFF000000000000)) shl 4);
  end;
end;

procedure MixColumns(var Q: TBS);
var q0, q1, q2, q3, q4, q5, q6, q7, r0, r1, r2, r3, r4, r5, r6, r7: UInt64;
begin
  q0 := Q[0]; q1 := Q[1]; q2 := Q[2]; q3 := Q[3]; q4 := Q[4]; q5 := Q[5]; q6 := Q[6]; q7 := Q[7];
  r0 := Ror64(q0, 16); r1 := Ror64(q1, 16); r2 := Ror64(q2, 16); r3 := Ror64(q3, 16);
  r4 := Ror64(q4, 16); r5 := Ror64(q5, 16); r6 := Ror64(q6, 16); r7 := Ror64(q7, 16);
  Q[0] := q7 xor r7 xor r0 xor Ror64(q0 xor r0, 32);
  Q[1] := q0 xor r0 xor q7 xor r7 xor r1 xor Ror64(q1 xor r1, 32);
  Q[2] := q1 xor r1 xor r2 xor Ror64(q2 xor r2, 32);
  Q[3] := q2 xor r2 xor q7 xor r7 xor r3 xor Ror64(q3 xor r3, 32);
  Q[4] := q3 xor r3 xor q7 xor r7 xor r4 xor Ror64(q4 xor r4, 32);
  Q[5] := q4 xor r4 xor r5 xor Ror64(q5 xor r5, 32);
  Q[6] := q5 xor r5 xor r6 xor Ror64(q6 xor r6, 32);
  Q[7] := q6 xor r6 xor r7 xor Ror64(q7 xor r7, 32);
end;

procedure AddRoundKey(var Q: TBS; const K: TAesKey; Off: Integer); inline;
var i: Integer;
begin
  for i := 0 to 7 do Q[i] := Q[i] xor K.SK[Off + i];
end;

function SubWord(X: UInt32): UInt32;
var Q: TBS;
begin
  FillChar(Q, SizeOf(Q), 0);
  Q[0] := X;
  Ortho(Q); Sbox(Q); Ortho(Q);
  Result := UInt32(Q[0]);
end;

procedure AesSetKey(out K: TAesKey; const Key: TBytes);
const
  M1 = UInt64($1111111111111111); M2 = UInt64($2222222222222222);
  M4 = UInt64($4444444444444444); M8 = UInt64($8888888888888888);
var
  nk, nkf, i, j, rk, v: Integer; tmp: UInt32;
  sk32: array[0..59] of UInt32;
  comp: array[0..29] of UInt64;
  Q: TBS; x0, x1, x2, x3: UInt64;
begin
  FillChar(K, SizeOf(K), 0);
  case Length(Key) of
    16: K.Rounds := 10;
    24: K.Rounds := 12;
    32: K.Rounds := 14;
  else raise Exception.Create('XelSSL AES: invalid key length');
  end;
  nk := Length(Key) shr 2;
  nkf := (K.Rounds + 1) shl 2;
  tmp := 0;
  for i := 0 to nk - 1 do begin tmp := LE32(@Key[i * 4]); sk32[i] := tmp; end;
  j := 0; rk := 0;
  for i := nk to nkf - 1 do
  begin
    if j = 0 then
    begin
      tmp := (tmp shl 24) or (tmp shr 8);         // RotWord in little-endian order
      tmp := SubWord(tmp) xor RCon[rk];
    end
    else if (nk > 6) and (j = 4) then
      tmp := SubWord(tmp);
    tmp := tmp xor sk32[i - nk];
    sk32[i] := tmp;
    Inc(j);
    if j = nk then begin j := 0; Inc(rk); end;
  end;
  // compressed round keys: 2 words per round
  i := 0; j := 0;
  while i < nkf do
  begin
    InterleaveIn(sk32[i], sk32[i + 1], sk32[i + 2], sk32[i + 3], Q[0], Q[4]);
    Q[1] := Q[0]; Q[2] := Q[0]; Q[3] := Q[0];
    Q[5] := Q[4]; Q[6] := Q[4]; Q[7] := Q[4];
    Ortho(Q);
    comp[j] := (Q[0] and M1) or (Q[1] and M2) or (Q[2] and M4) or (Q[3] and M8);
    comp[j + 1] := (Q[4] and M1) or (Q[5] and M2) or (Q[6] and M4) or (Q[7] and M8);
    Inc(i, 4); Inc(j, 2);
  end;
  // expand to the full bitsliced form
  v := 0;
  for i := 0 to (K.Rounds + 1) * 2 - 1 do
  begin
    x0 := comp[i] and M1; x1 := (comp[i] and M2) shr 1;
    x2 := (comp[i] and M4) shr 2; x3 := (comp[i] and M8) shr 3;
    K.SK[v] := (x0 shl 4) - x0; K.SK[v + 1] := (x1 shl 4) - x1;
    K.SK[v + 2] := (x2 shl 4) - x2; K.SK[v + 3] := (x3 shl 4) - x3;
    Inc(v, 4);
  end;
  FillChar(sk32, SizeOf(sk32), 0); FillChar(comp, SizeOf(comp), 0); FillChar(Q, SizeOf(Q), 0);
end;

procedure EncryptLanes(const K: TAesKey; Src, Dst: PByte; N: Integer);
var Q: TBS; w0, w1, w2, w3: UInt32; i, u: Integer;
begin
  FillChar(Q, SizeOf(Q), 0);
  for i := 0 to N - 1 do
    InterleaveIn(LE32(Src + i * 16), LE32(Src + i * 16 + 4), LE32(Src + i * 16 + 8),
      LE32(Src + i * 16 + 12), Q[i], Q[i + 4]);
  Ortho(Q);
  AddRoundKey(Q, K, 0);
  for u := 1 to K.Rounds - 1 do
  begin
    Sbox(Q); ShiftRows(Q); MixColumns(Q);
    AddRoundKey(Q, K, u shl 3);
  end;
  Sbox(Q); ShiftRows(Q);
  AddRoundKey(Q, K, K.Rounds shl 3);
  Ortho(Q);
  for i := 0 to N - 1 do
  begin
    InterleaveOut(w0, w1, w2, w3, Q[i], Q[i + 4]);
    PutLE32(Dst + i * 16, w0); PutLE32(Dst + i * 16 + 4, w1);
    PutLE32(Dst + i * 16 + 8, w2); PutLE32(Dst + i * 16 + 12, w3);
  end;
  FillChar(Q, SizeOf(Q), 0);
end;

procedure AesEncryptBlocks(const K: TAesKey; Src, Dst: PByte; N: Integer);
begin
  while N >= 4 do
  begin
    EncryptLanes(K, Src, Dst, 4);
    Inc(Src, 64); Inc(Dst, 64); Dec(N, 4);
  end;
  if N > 0 then EncryptLanes(K, Src, Dst, N);
end;

// ================= GHASH =================

function BitRev64(X: UInt64): UInt64;
begin
  X := ((X shr 1) and UInt64($5555555555555555)) or ((X and UInt64($5555555555555555)) shl 1);
  X := ((X shr 2) and UInt64($3333333333333333)) or ((X and UInt64($3333333333333333)) shl 2);
  X := ((X shr 4) and UInt64($0F0F0F0F0F0F0F0F)) or ((X and UInt64($0F0F0F0F0F0F0F0F)) shl 4);
  X := ((X shr 8) and UInt64($00FF00FF00FF00FF)) or ((X and UInt64($00FF00FF00FF00FF)) shl 8);
  X := ((X shr 16) and UInt64($0000FFFF0000FFFF)) or ((X and UInt64($0000FFFF0000FFFF)) shl 16);
  Result := (X shr 32) or (X shl 32);
end;

// carry-less 64x64 multiply -> low 64 bits, no branches or tables
function ClMul64(X, Y: UInt64): UInt64;
var x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3: UInt64;
begin
  x0 := X and UInt64($1111111111111111); x1 := X and UInt64($2222222222222222);
  x2 := X and UInt64($4444444444444444); x3 := X and UInt64($8888888888888888);
  y0 := Y and UInt64($1111111111111111); y1 := Y and UInt64($2222222222222222);
  y2 := Y and UInt64($4444444444444444); y3 := Y and UInt64($8888888888888888);
  z0 := (x0 * y0) xor (x1 * y3) xor (x2 * y2) xor (x3 * y1);
  z1 := (x0 * y1) xor (x1 * y0) xor (x2 * y3) xor (x3 * y2);
  z2 := (x0 * y2) xor (x1 * y1) xor (x2 * y0) xor (x3 * y3);
  z3 := (x0 * y3) xor (x1 * y2) xor (x2 * y1) xor (x3 * y0);
  Result := (z0 and UInt64($1111111111111111)) or (z1 and UInt64($2222222222222222)) or
            (z2 and UInt64($4444444444444444)) or (z3 and UInt64($8888888888888888));
end;

// X := X * H in GF(2^128), GCM representation (bit-reflected), as TGcmUtilities.Multiply
procedure GfMul(var X0, X1: UInt64; H0, H1: UInt64);
var x0r, x1r, y0r, y1r, h_0, h_1, h_2, h_3, h_4, h_5, z0, z1, z2, z3: UInt64;
begin
  x0r := BitRev64(X0); x1r := BitRev64(X1); y0r := BitRev64(H0); y1r := BitRev64(H1);
  h_0 := BitRev64(ClMul64(x0r, y0r));
  h_1 := ClMul64(X0, H0) shl 1;
  h_2 := BitRev64(ClMul64(x1r, y1r));
  h_3 := ClMul64(X1, H1) shl 1;
  h_4 := BitRev64(ClMul64(x0r xor x1r, y0r xor y1r));
  h_5 := ClMul64(X0 xor X1, H0 xor H1) shl 1;
  z0 := h_0;
  z1 := h_1 xor h_0 xor h_2 xor h_4;
  z2 := h_2 xor h_1 xor h_3 xor h_5;
  z3 := h_3;
  z1 := z1 xor z3 xor (z3 shr 1) xor (z3 shr 2) xor (z3 shr 7);
  z2 := z2 xor (z3 shl 62) xor (z3 shl 57);
  z0 := z0 xor z2 xor (z2 shr 1) xor (z2 shr 2) xor (z2 shr 7);
  z1 := z1 xor (z2 shl 63) xor (z2 shl 62) xor (z2 shl 57);
  X0 := z0; X1 := z1;
end;

function BE64(P: PByte): UInt64; inline;
var i: Integer;
begin
  Result := 0;
  for i := 0 to 7 do Result := (Result shl 8) or P[i];
end;

procedure PutBE64(P: PByte; V: UInt64); inline;
var i: Integer;
begin
  for i := 7 downto 0 do begin P[i] := Byte(V); V := V shr 8; end;
end;

procedure GhashData(const G: TGcmKey; var Y0, Y1: UInt64; const Data: TBytes);
var i, n, r: Integer; blk: array[0..15] of Byte;
begin
  n := Length(Data) div 16;
  for i := 0 to n - 1 do
  begin
    Y0 := Y0 xor BE64(@Data[i * 16]);
    Y1 := Y1 xor BE64(@Data[i * 16 + 8]);
    GfMul(Y0, Y1, G.H0, G.H1);
  end;
  r := Length(Data) - n * 16;
  if r > 0 then
  begin
    FillChar(blk, 16, 0);
    Move(Data[n * 16], blk[0], r);
    Y0 := Y0 xor BE64(@blk[0]);
    Y1 := Y1 xor BE64(@blk[8]);
    GfMul(Y0, Y1, G.H0, G.H1);
  end;
end;

procedure GcmSetKey(out G: TGcmKey; const Key: TBytes);
var z: array[0..15] of Byte;
begin
  AesSetKey(G.Aes, Key);
  FillChar(z, 16, 0);
  AesEncryptBlocks(G.Aes, @z[0], @z[0], 1);
  G.H0 := BE64(@z[0]);
  G.H1 := BE64(@z[8]);
end;

// CTR: 32-bit big-endian counter in the last 4 bytes of block J0 = nonce || ctr
procedure GcmCtr(const G: TGcmKey; const Nonce: TBytes; StartCtr: UInt32;
  Src, Dst: PByte; Len: Integer);
var ctrs, ks: array[0..63] of Byte; i, nb, take, k: Integer; c: UInt32;
begin
  c := StartCtr;
  while Len > 0 do
  begin
    nb := (Len + 15) div 16;
    if nb > 4 then nb := 4;
    for i := 0 to nb - 1 do
    begin
      Move(Nonce[0], ctrs[i * 16], 12);
      ctrs[i * 16 + 12] := Byte(c shr 24); ctrs[i * 16 + 13] := Byte(c shr 16);
      ctrs[i * 16 + 14] := Byte(c shr 8); ctrs[i * 16 + 15] := Byte(c);
      Inc(c);
    end;
    AesEncryptBlocks(G.Aes, @ctrs[0], @ks[0], nb);
    take := nb * 16;
    if take > Len then take := Len;
    for k := 0 to take - 1 do Dst[k] := Src[k] xor ks[k];
    Inc(Src, take); Inc(Dst, take); Dec(Len, take);
  end;
  FillChar(ks, SizeOf(ks), 0);
end;

function GcmTag(const G: TGcmKey; const Nonce, AAD, Cipher: TBytes): TBytes;
var y0, y1: UInt64; lenblk: array[0..15] of Byte; j0, s: array[0..15] of Byte; i: Integer;
begin
  y0 := 0; y1 := 0;
  GhashData(G, y0, y1, AAD);
  GhashData(G, y0, y1, Cipher);
  PutBE64(@lenblk[0], UInt64(Length(AAD)) * 8);
  PutBE64(@lenblk[8], UInt64(Length(Cipher)) * 8);
  y0 := y0 xor BE64(@lenblk[0]); y1 := y1 xor BE64(@lenblk[8]);
  GfMul(y0, y1, G.H0, G.H1);
  // tag = GHASH xor E(K, J0), J0 = nonce || 00000001
  Move(Nonce[0], j0[0], 12);
  j0[12] := 0; j0[13] := 0; j0[14] := 0; j0[15] := 1;
  AesEncryptBlocks(G.Aes, @j0[0], @s[0], 1);
  SetLength(Result, 16);
  PutBE64(@Result[0], y0); PutBE64(@Result[8], y1);
  for i := 0 to 15 do Result[i] := Result[i] xor s[i];
end;

function GcmSeal(const G: TGcmKey; const Nonce, AAD, Plain: TBytes): TBytes;
var c, t: TBytes;
begin
  if Length(Nonce) <> 12 then raise Exception.Create('XelSSL GCM: nonce must be 12 bytes');
  SetLength(c, Length(Plain));
  if Length(Plain) > 0 then GcmCtr(G, Nonce, 2, @Plain[0], @c[0], Length(Plain));
  t := GcmTag(G, Nonce, AAD, c);
  Result := Concat(c, t);
end;

function GcmOpen(const G: TGcmKey; const Nonce, AAD, Data: TBytes; out Plain: TBytes): Boolean;
var c, t, tt: TBytes; d: Byte; i: Integer;
begin
  Plain := nil;
  if (Length(Nonce) <> 12) or (Length(Data) < 16) then Exit(False);
  c := Copy(Data, 0, Length(Data) - 16);
  t := Copy(Data, Length(Data) - 16, 16);
  tt := GcmTag(G, Nonce, AAD, c);
  d := 0;
  for i := 0 to 15 do d := d or (t[i] xor tt[i]);       // constant-time comparison
  if d <> 0 then Exit(False);
  SetLength(Plain, Length(c));
  if Length(c) > 0 then GcmCtr(G, Nonce, 2, @c[0], @Plain[0], Length(c));
  Result := True;
end;

end.
