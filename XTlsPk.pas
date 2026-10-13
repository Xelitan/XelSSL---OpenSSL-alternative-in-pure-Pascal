// XTls - signature verification: RSA PKCS#1 v1.5, RSA-PSS (RFC 8017),
// ECDSA on P-256 / P-384 / P-521 (FIPS 186-4). Public data only.
// Curve parameters: SEC 2 (copied from CryptoLib4Pascal, MIT). License: MIT.
unit XTlsPk;

{$mode objfpc}{$H+}{$Q-}{$R-}

interface

uses
  SysUtils, XTlsHash, XTlsBigNum;

type
  TEcCurveId = (ecNone, ecP256, ecP384, ecP521);

// Hashed = message digest (already computed with Alg).
function RsaPkcs1Verify(const N, E: TBytes; Alg: THashAlg; const Hashed, Sig: TBytes): Boolean;
// SaltLen < 0: any salt length (read from the signature). MGF1 with the same hash.
function RsaPssVerify(const N, E: TBytes; Alg: THashAlg; const Hashed, Sig: TBytes; SaltLen: Integer): Boolean;
// Pub = uncompressed point 04||X||Y; SigDer = SEQUENCE{INTEGER r, INTEGER s}.
function EcdsaVerify(Curve: TEcCurveId; const Pub, Hashed, SigDer: TBytes): Boolean;
function EcCoordLen(Curve: TEcCurveId): Integer;

implementation

// ================= RSA =================

const
  // DigestInfo DER (RFC 8017 9.2, note 1)
  DI_SHA1   = '3021300906052b0e03021a05000414';
  DI_SHA256 = '3031300d060960864801650304020105000420';
  DI_SHA384 = '3041300d060960864801650304020205000430';
  DI_SHA512 = '3051300d060960864801650304020305000440';

function RsaPublic(const N, E, Sig: TBytes; out EM: TBytes): Boolean;
var bn, be, bs: TBig;
begin
  Result := False; EM := nil;
  bn := BigFromBytes(N); be := BigFromBytes(E); bs := BigFromBytes(Sig);
  if (BigBits(bn) < 1024) or (Length(Sig) <> (BigBits(bn) + 7) div 8) then Exit;   // min. 1024 bits
  if BigCmp(bs, bn) >= 0 then Exit;
  EM := BigToBytes(BigModExp(bs, be, bn), Length(Sig));
  Result := True;
end;

function RsaPkcs1Verify(const N, E: TBytes; Alg: THashAlg; const Hashed, Sig: TBytes): Boolean;
var em, exp, di: TBytes; k, i: Integer;
begin
  Result := False;
  if not RsaPublic(N, E, Sig, em) then Exit;
  case Alg of
    haSHA1: di := FromHex(DI_SHA1);
    haSHA256: di := FromHex(DI_SHA256);
    haSHA384: di := FromHex(DI_SHA384);
  else di := FromHex(DI_SHA512);
  end;
  if Length(Hashed) <> HashSize(Alg) then Exit;
  di := Concat(di, Hashed);
  k := Length(em);
  if k < Length(di) + 11 then Exit;
  // build the expected EM = 00 01 FF..FF 00 DigestInfo and compare it whole
  SetLength(exp, k);
  exp[0] := 0; exp[1] := 1;
  for i := 2 to k - Length(di) - 2 do exp[i] := $FF;
  exp[k - Length(di) - 1] := 0;
  Move(di[0], exp[k - Length(di)], Length(di));
  Result := SameBytesCT(em, exp);
end;

function Mgf1(Alg: THashAlg; const Seed: TBytes; Len: Integer): TBytes;
var c: UInt32; t, blk: TBytes; off: Integer;
begin
  SetLength(Result, Len);
  c := 0; off := 0;
  while off < Len do
  begin
    blk := Concat(Seed, TBytes.Create(Byte(c shr 24), Byte(c shr 16), Byte(c shr 8), Byte(c)));
    t := Hash(Alg, blk);
    if Len - off < Length(t) then Move(t[0], Result[off], Len - off) else Move(t[0], Result[off], Length(t));
    Inc(off, Length(t)); Inc(c);
  end;
end;

function RsaPssVerify(const N, E: TBytes; Alg: THashAlg; const Hashed, Sig: TBytes; SaltLen: Integer): Boolean;
var
  em, db, h, mask, salt, m2: TBytes;
  modBits, emBits, emLen, hLen, i, ps, topBits: Integer;
begin
  Result := False;
  if not RsaPublic(N, E, Sig, em) then Exit;
  hLen := HashSize(Alg);
  if Length(Hashed) <> hLen then Exit;
  modBits := BigBits(BigFromBytes(N));
  emBits := modBits - 1;
  emLen := (emBits + 7) div 8;
  if Length(em) > emLen then          // modBits = 8k+1: the leading byte must be zero
  begin
    if em[0] <> 0 then Exit;
    em := Copy(em, 1, emLen);
  end;
  if emLen < hLen + 2 then Exit;
  if em[emLen - 1] <> $BC then Exit;
  db := Copy(em, 0, emLen - hLen - 1);
  h := Copy(em, emLen - hLen - 1, hLen);
  topBits := 8 * emLen - emBits;
  if (db[0] and not ($FF shr topBits)) <> 0 then Exit;
  mask := Mgf1(Alg, h, Length(db));
  for i := 0 to High(db) do db[i] := db[i] xor mask[i];
  db[0] := db[0] and ($FF shr topBits);
  // DB = 00..00 || 01 || salt
  ps := 0;
  while (ps < Length(db)) and (db[ps] = 0) do Inc(ps);
  if (ps >= Length(db)) or (db[ps] <> 1) then Exit;
  salt := Copy(db, ps + 1, Length(db) - ps - 1);
  if (SaltLen >= 0) and (Length(salt) <> SaltLen) then Exit;
  SetLength(m2, 8); FillChar(m2[0], 8, 0);
  m2 := Concat(m2, Hashed, salt);
  Result := SameBytesCT(Hash(Alg, m2), h);
end;

// ================= ECDSA =================

type
  TCurve = record
    P, B, N, Gx, Gy: TBig;
    Len: Integer;                  // coordinate bytes
  end;
  TJac = record X, Y, Z: TBig; end;   // Z = 0 -> point at infinity

function GetCurve(Id: TEcCurveId; out C: TCurve): Boolean;
begin
  Result := True;
  case Id of
    ecP256:
      begin
        C.P := BigFromHex('FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF');
        C.B := BigFromHex('5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B');
        C.N := BigFromHex('FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551');
        C.Gx := BigFromHex('6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296');
        C.Gy := BigFromHex('4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5');
        C.Len := 32;
      end;
    ecP384:
      begin
        C.P := BigFromHex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFF0000000000000000FFFFFFFF');
        C.B := BigFromHex('B3312FA7E23EE7E4988E056BE3F82D19181D9C6EFE8141120314088F5013875AC656398D8A2ED19D2A85C8EDD3EC2AEF');
        C.N := BigFromHex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973');
        C.Gx := BigFromHex('AA87CA22BE8B05378EB1C71EF320AD746E1D3B628BA79B9859F741E082542A385502F25DBF55296C3A545E3872760AB7');
        C.Gy := BigFromHex('3617DE4A96262C6F5D9E98BF9292DC29F8F41DBD289A147CE9DA3113B5F0B8C00A60B1CE1D7E819D7A431D7C90EA0E5F');
        C.Len := 48;
      end;
    ecP521:
      begin
        C.P := BigFromHex('01FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF');
        C.B := BigFromHex('0051953EB9618E1C9A1F929A21A0B68540EEA2DA725B99B315F3B8B489918EF109E156193951EC7E937B1652C0BD3BB1BF073573DF883D2C34F1EF451FD46B503F00');
        C.N := BigFromHex('01FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFA51868783BF2F966B7FCC0148F709A5D03BB5C9B8899C47AEBB6FB71E91386409');
        C.Gx := BigFromHex('00C6858E06B70404E9CD9E3ECB662395B4429C648139053FB521F828AF606B4D3DBAA14B5E77EFE75928FE1DC127A2FFA8DE3348B3C1856A429BF97E7E31C2E5BD66');
        C.Gy := BigFromHex('011839296A789A3BC0045C8A5FB42C7D1BD998F54449579B446817AFBD17273E662C97EE72995EF42640C550B9013FAD0761353C7086A272C24088BE94769FD16650');
        C.Len := 66;
      end;
  else Result := False;
  end;
end;

function EcCoordLen(Curve: TEcCurveId): Integer;
begin
  case Curve of
    ecP256: Result := 32;
    ecP384: Result := 48;
    ecP521: Result := 66;
  else Result := 0;
  end;
end;

// doubling, a = -3 (dbl-2001-b)
function JDouble(const C: TCurve; const A: TJac): TJac;
var delta, gamma, beta, alpha, t, p: TBig;
begin
  p := C.P;
  if BigIsZero(A.Z) or BigIsZero(A.Y) then begin Result.X := nil; Result.Y := BigFromInt(1); Result.Z := nil; Exit; end;
  delta := BigModMul(A.Z, A.Z, p);
  gamma := BigModMul(A.Y, A.Y, p);
  beta := BigModMul(A.X, gamma, p);
  t := BigModMul(BigModSub(A.X, delta, p), BigModAdd(A.X, delta, p), p);
  alpha := BigModAdd(BigModAdd(t, t, p), t, p);
  t := BigModAdd(beta, beta, p); t := BigModAdd(t, t, p); t := BigModAdd(t, t, p);   // 8*beta
  Result.X := BigModSub(BigModMul(alpha, alpha, p), t, p);
  t := BigModAdd(A.Y, A.Z, p);
  Result.Z := BigModSub(BigModSub(BigModMul(t, t, p), gamma, p), delta, p);
  t := BigModAdd(beta, beta, p); t := BigModAdd(t, t, p);                           // 4*beta
  gamma := BigModMul(gamma, gamma, p);
  gamma := BigModAdd(gamma, gamma, p); gamma := BigModAdd(gamma, gamma, p); gamma := BigModAdd(gamma, gamma, p); // 8*gamma^2
  Result.Y := BigModSub(BigModMul(alpha, BigModSub(t, Result.X, p), p), gamma, p);
end;

// addition (add-2007-bl)
function JAdd(const C: TCurve; const A, B: TJac): TJac;
var z1z1, z2z2, u1, u2, s1, s2, h, i, j, r, v, t, p: TBig;
begin
  p := C.P;
  if BigIsZero(A.Z) then Exit(B);
  if BigIsZero(B.Z) then Exit(A);
  z1z1 := BigModMul(A.Z, A.Z, p);
  z2z2 := BigModMul(B.Z, B.Z, p);
  u1 := BigModMul(A.X, z2z2, p);
  u2 := BigModMul(B.X, z1z1, p);
  s1 := BigModMul(BigModMul(A.Y, B.Z, p), z2z2, p);
  s2 := BigModMul(BigModMul(B.Y, A.Z, p), z1z1, p);
  h := BigModSub(u2, u1, p);
  r := BigModSub(s2, s1, p);
  if BigIsZero(h) then
  begin
    if BigIsZero(r) then Exit(JDouble(C, A));
    Result.X := nil; Result.Y := BigFromInt(1); Result.Z := nil; Exit;      // P + (-P)
  end;
  r := BigModAdd(r, r, p);
  t := BigModAdd(h, h, p);
  i := BigModMul(t, t, p);
  j := BigModMul(h, i, p);
  v := BigModMul(u1, i, p);
  Result.X := BigModSub(BigModSub(BigModMul(r, r, p), j, p), BigModAdd(v, v, p), p);
  t := BigModMul(s1, j, p);
  Result.Y := BigModSub(BigModMul(r, BigModSub(v, Result.X, p), p), BigModAdd(t, t, p), p);
  t := BigModAdd(A.Z, B.Z, p);
  Result.Z := BigModMul(BigModSub(BigModSub(BigModMul(t, t, p), z1z1, p), z2z2, p), h, p);
end;

function OnCurve(const C: TCurve; const X, Y: TBig): Boolean;
var l, r, x3, three: TBig;
begin
  // y^2 = x^3 - 3x + b
  if (BigCmp(X, C.P) >= 0) or (BigCmp(Y, C.P) >= 0) then Exit(False);
  l := BigModMul(Y, Y, C.P);
  x3 := BigModMul(BigModMul(X, X, C.P), X, C.P);
  three := BigModMul(BigFromInt(3), X, C.P);
  r := BigModAdd(BigModSub(x3, three, C.P), C.B, C.P);
  Result := BigCmp(l, r) = 0;
end;

// simple parser for SEQUENCE { INTEGER r, INTEGER s }
function ParseEcdsaSig(const D: TBytes; out R, S: TBig): Boolean;
var pos: Integer;
  function ReadLen(out L: Integer): Boolean;
  var nb, k: Integer;
  begin
    Result := False;
    if pos >= Length(D) then Exit;
    L := D[pos]; Inc(pos);
    if L < $80 then Exit(True);
    nb := L and $7F;
    if (nb = 0) or (nb > 2) or (pos + nb > Length(D)) then Exit;
    L := 0;
    for k := 1 to nb do begin L := (L shl 8) or D[pos]; Inc(pos); end;
    Result := True;
  end;
  function ReadInt(out V: TBig): Boolean;
  var l: Integer;
  begin
    Result := False;
    if (pos >= Length(D)) or (D[pos] <> $02) then Exit;
    Inc(pos);
    if not ReadLen(l) or (l = 0) or (pos + l > Length(D)) then Exit;
    if (D[pos] and $80) <> 0 then Exit;                 // negative
    V := BigFromBytes(Copy(D, pos, l));
    Inc(pos, l);
    Result := True;
  end;
var l: Integer;
begin
  Result := False; pos := 0;
  if (Length(D) < 8) or (D[0] <> $30) then Exit;
  Inc(pos);
  if not ReadLen(l) or (pos + l <> Length(D)) then Exit;
  if not ReadInt(R) then Exit;
  if not ReadInt(S) then Exit;
  Result := pos = Length(D);
end;

function EcdsaVerify(Curve: TEcCurveId; const Pub, Hashed, SigDer: TBytes): Boolean;
var
  C: TCurve; qx, qy, r, s, e, w, u1, u2, zinv, x: TBig;
  G, Q, GQ, Acc: TJac; i, nb: Integer;
begin
  Result := False;
  if not GetCurve(Curve, C) then Exit;
  if (Length(Pub) <> 1 + 2 * C.Len) or (Pub[0] <> 4) then Exit;
  qx := BigFromBytes(Copy(Pub, 1, C.Len));
  qy := BigFromBytes(Copy(Pub, 1 + C.Len, C.Len));
  if not OnCurve(C, qx, qy) then Exit;
  if not ParseEcdsaSig(SigDer, r, s) then Exit;
  if BigIsZero(r) or BigIsZero(s) or (BigCmp(r, C.N) >= 0) or (BigCmp(s, C.N) >= 0) then Exit;
  // e = leftmost bits of the hash (as many as n has)
  e := BigFromBytes(Hashed);
  nb := BigBits(C.N);
  if Length(Hashed) * 8 > nb then e := BigShr(e, Length(Hashed) * 8 - nb);
  w := BigModInvPrime(s, C.N);
  u1 := BigModMul(e, w, C.N);
  u2 := BigModMul(r, w, C.N);
  G.X := C.Gx; G.Y := C.Gy; G.Z := BigFromInt(1);
  Q.X := qx; Q.Y := qy; Q.Z := BigFromInt(1);
  GQ := JAdd(C, G, Q);
  Acc.X := nil; Acc.Y := BigFromInt(1); Acc.Z := nil;
  // Shamir's trick: u1*G + u2*Q in a single pass
  for i := nb - 1 downto 0 do
  begin
    Acc := JDouble(C, Acc);
    if (BigBit(u1, i) = 1) and (BigBit(u2, i) = 1) then Acc := JAdd(C, Acc, GQ)
    else if BigBit(u1, i) = 1 then Acc := JAdd(C, Acc, G)
    else if BigBit(u2, i) = 1 then Acc := JAdd(C, Acc, Q);
  end;
  if BigIsZero(Acc.Z) then Exit;
  zinv := BigModInvPrime(Acc.Z, C.P);
  x := BigModMul(Acc.X, BigModMul(zinv, zinv, C.P), C.P);
  Result := BigCmp(BigMod(x, C.N), r) = 0;
end;

end.
