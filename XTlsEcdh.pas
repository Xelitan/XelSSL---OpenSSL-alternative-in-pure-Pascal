// XTls - ECDH on the NIST curves P-256 / P-384 / P-521 (TLS key exchange).
// Constant-time arithmetic: 32-bit limbs (8/12/17), Montgomery multiplication
// (CIOS; for all three p = -1 mod 2^32, so -p^-1 mod 2^32 = 1), conditional
// subtraction via masks, Montgomery ladder with branch-free swaps.
// Jacobian coordinates, a = -3. Curve parameters: SEC 2. License: MIT.
unit XTlsEcdh;

{$mode objfpc}{$H+}{$Q-}{$R-}

interface

uses
  SysUtils;

type
  TEcdhCurve = (ecdhP256, ecdhP384, ecdhP521);

// New key pair: Priv = scalar (Len bytes), Pub = 04||X||Y.
procedure EcdhKeyPair(Curve: TEcdhCurve; out Priv, Pub: TBytes);
// Shared secret = X coordinate. False if the peer's point is invalid.
function EcdhShared(Curve: TEcdhCurve; const Priv, PeerPub: TBytes; out Secret: TBytes): Boolean;
// Public key for a given scalar (tests).
function EcdhPublicOf(Curve: TEcdhCurve; const Priv: TBytes): TBytes;
function EcdhCoordLen(Curve: TEcdhCurve): Integer;

implementation

uses XTlsRandom, XTlsBigNum;

const
  MAXL = 17;

type
  TFe = array[0..MAXL - 1] of UInt32;      // little-endian; NL limbs used
  TPt = record X, Y, Z: TFe; end;
  TCtx = record
    NL, Len, NBits: Integer;               // limbs, coordinate bytes, bits of the order n
    P, R2, OneM, BM, GX, GY: TFe;
    N: TBig;
    Ready: Boolean;
  end;

var
  Ctxs: array[TEcdhCurve] of TCtx;

const
  Hex: array[TEcdhCurve, 0..4] of string = (
    ('FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF',
     '5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B',
     'FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551',
     '6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296',
     '4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5'),
    ('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFF0000000000000000FFFFFFFF',
     'B3312FA7E23EE7E4988E056BE3F82D19181D9C6EFE8141120314088F5013875AC656398D8A2ED19D2A85C8EDD3EC2AEF',
     'FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973',
     'AA87CA22BE8B05378EB1C71EF320AD746E1D3B628BA79B9859F741E082542A385502F25DBF55296C3A545E3872760AB7',
     '3617DE4A96262C6F5D9E98BF9292DC29F8F41DBD289A147CE9DA3113B5F0B8C00A60B1CE1D7E819D7A431D7C90EA0E5F'),
    ('01FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF',
     '0051953EB9618E1C9A1F929A21A0B68540EEA2DA725B99B315F3B8B489918EF109E156193951EC7E937B1652C0BD3BB1BF073573DF883D2C34F1EF451FD46B503F00',
     '01FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFA51868783BF2F966B7FCC0148F709A5D03BB5C9B8899C47AEBB6FB71E91386409',
     '00C6858E06B70404E9CD9E3ECB662395B4429C648139053FB521F828AF606B4D3DBAA14B5E77EFE75928FE1DC127A2FFA8DE3348B3C1856A429BF97E7E31C2E5BD66',
     '011839296A789A3BC0045C8A5FB42C7D1BD998F54449579B446817AFBD17273E662C97EE72995EF42640C550B9013FAD0761353C7086A272C24088BE94769FD16650'));

// ---- conversions ----

procedure FeFromBig(const C: TCtx; out R: TFe; const B: TBig);
var i: Integer;
begin
  FillChar(R, SizeOf(R), 0);
  for i := 0 to C.NL - 1 do
    if i < Length(B) then R[i] := B[i];
end;

function FeToBig(const C: TCtx; const A: TFe): TBig;
var i, n: Integer;
begin
  SetLength(Result, C.NL);
  for i := 0 to C.NL - 1 do Result[i] := A[i];
  n := C.NL;
  while (n > 0) and (Result[n - 1] = 0) do Dec(n);
  SetLength(Result, n);
end;

// ---- arithmetic mod p (constant time; loops depend only on NL) ----

procedure FeReduceOnce(const C: TCtx; var A: TFe; Hi: UInt32);
var t: TFe; i: Integer; d: Int64; borrow, mask: UInt32;
begin
  borrow := 0;
  for i := 0 to C.NL - 1 do
  begin
    d := Int64(A[i]) - C.P[i] - borrow;
    t[i] := UInt32(d);
    borrow := UInt32(QWord(d) shr 63);
  end;
  mask := UInt32(0) - ((Hi or (borrow xor 1)) and 1);
  for i := 0 to C.NL - 1 do A[i] := (t[i] and mask) or (A[i] and not mask);
end;

procedure FeAdd(const C: TCtx; out R: TFe; const A, B: TFe);
var i: Integer; cy: UInt64;
begin
  cy := 0;
  for i := 0 to C.NL - 1 do
  begin
    cy := cy + A[i] + B[i];
    R[i] := UInt32(cy);
    cy := cy shr 32;
  end;
  FeReduceOnce(C, R, UInt32(cy));
end;

procedure FeSub(const C: TCtx; out R: TFe; const A, B: TFe);
var i: Integer; d: Int64; borrow, mask: UInt32; cy: UInt64;
begin
  borrow := 0;
  for i := 0 to C.NL - 1 do
  begin
    d := Int64(A[i]) - B[i] - borrow;
    R[i] := UInt32(d);
    borrow := UInt32(QWord(d) shr 63);
  end;
  mask := UInt32(0) - borrow;
  cy := 0;
  for i := 0 to C.NL - 1 do
  begin
    cy := cy + R[i] + (C.P[i] and mask);
    R[i] := UInt32(cy);
    cy := cy shr 32;
  end;
end;

// Montgomery: R := A*B*2^(-32*NL) mod p
procedure FeMul(const C: TCtx; out R: TFe; const A, B: TFe);
var t: array[0..MAXL + 1] of UInt32; i, j, nl: Integer; cy: UInt64; m: UInt32;
begin
  nl := C.NL;
  for i := 0 to nl + 1 do t[i] := 0;
  for i := 0 to nl - 1 do
  begin
    cy := 0;
    for j := 0 to nl - 1 do
    begin
      cy := cy + t[j] + UInt64(A[j]) * B[i];
      t[j] := UInt32(cy);
      cy := cy shr 32;
    end;
    cy := cy + t[nl];
    t[nl] := UInt32(cy);
    t[nl + 1] := UInt32(cy shr 32);
    m := t[0];                                   // -p^-1 mod 2^32 = 1
    cy := (UInt64(t[0]) + UInt64(m) * C.P[0]) shr 32;
    for j := 1 to nl - 1 do
    begin
      cy := cy + t[j] + UInt64(m) * C.P[j];
      t[j - 1] := UInt32(cy);
      cy := cy shr 32;
    end;
    cy := cy + t[nl];
    t[nl - 1] := UInt32(cy);
    t[nl] := t[nl + 1] + UInt32(cy shr 32);
  end;
  FillChar(R, SizeOf(R), 0);
  for i := 0 to nl - 1 do R[i] := t[i];
  FeReduceOnce(C, R, t[nl]);
end;

procedure FeInv(const C: TCtx; out R: TFe; const A: TFe);
var e: TBig; i: Integer; acc: TFe;
begin
  e := BigSub(FeToBig(C, C.P), BigFromInt(2));    // public exponent
  acc := C.OneM;
  for i := 32 * C.NL - 1 downto 0 do
  begin
    FeMul(C, acc, acc, acc);
    if BigBit(e, i) = 1 then FeMul(C, acc, acc, A);
  end;
  R := acc;
end;

procedure FeCSwap(const C: TCtx; var A, B: TFe; Bit: UInt32);
var i: Integer; mask, t: UInt32;
begin
  mask := UInt32(0) - (Bit and 1);
  for i := 0 to C.NL - 1 do
  begin
    t := mask and (A[i] xor B[i]);
    A[i] := A[i] xor t; B[i] := B[i] xor t;
  end;
end;

function FeEq(const C: TCtx; const A, B: TFe): Boolean;
var i: Integer; d: UInt32;
begin
  d := 0;
  for i := 0 to C.NL - 1 do d := d or (A[i] xor B[i]);
  Result := d = 0;
end;

procedure InitCurve(Curve: TEcdhCurve);
var c: TCtx; one, t: TFe;
begin
  begin
    c := Default(TCtx);
    case Curve of
      ecdhP256: begin c.NL := 8; c.Len := 32; end;
      ecdhP384: begin c.NL := 12; c.Len := 48; end;
      ecdhP521: begin c.NL := 17; c.Len := 66; end;
    end;
    FeFromBig(c, c.P, BigFromHex(Hex[Curve, 0]));
    c.N := BigFromHex(Hex[Curve, 2]);
    c.NBits := BigBits(c.N);
    // R^2 mod p, R = 2^(32*NL)
    FeFromBig(c, c.R2, BigMod(BigFromHex('1' + StringOfChar('0', 16 * c.NL)), BigFromHex(Hex[Curve, 0])));
    FillChar(one, SizeOf(one), 0); one[0] := 1;
    FeMul(c, c.OneM, one, c.R2);
    FeFromBig(c, t, BigFromHex(Hex[Curve, 1])); FeMul(c, c.BM, t, c.R2);
    FeFromBig(c, t, BigFromHex(Hex[Curve, 3])); FeMul(c, c.GX, t, c.R2);
    FeFromBig(c, t, BigFromHex(Hex[Curve, 4])); FeMul(c, c.GY, t, c.R2);
    c.Ready := True;
    Ctxs[Curve] := c;
  end;
end;

// contexts computed once in the initialization section - thread-safe
function Ctx(Curve: TEcdhCurve): TCtx;
begin
  Result := Ctxs[Curve];
end;

function EcdhCoordLen(Curve: TEcdhCurve): Integer;
begin
  case Curve of
    ecdhP256: Result := 32;
    ecdhP384: Result := 48;
  else Result := 66;
  end;
end;

// ---- points (Jacobian, a = -3) ----

procedure PtDouble(const C: TCtx; out R: TPt; const A: TPt);
var delta, gamma, beta, alpha, t, t2: TFe;
begin
  FeMul(C, delta, A.Z, A.Z);
  FeMul(C, gamma, A.Y, A.Y);
  FeMul(C, beta, A.X, gamma);
  FeSub(C, t, A.X, delta); FeAdd(C, t2, A.X, delta); FeMul(C, alpha, t, t2);
  FeAdd(C, t, alpha, alpha); FeAdd(C, alpha, t, alpha);
  FeAdd(C, t, beta, beta); FeAdd(C, t, t, t); FeAdd(C, t2, t, t);
  FeMul(C, R.X, alpha, alpha); FeSub(C, R.X, R.X, t2);
  FeAdd(C, R.Z, A.Y, A.Z); FeMul(C, R.Z, R.Z, R.Z); FeSub(C, R.Z, R.Z, gamma); FeSub(C, R.Z, R.Z, delta);
  FeMul(C, gamma, gamma, gamma); FeAdd(C, gamma, gamma, gamma); FeAdd(C, gamma, gamma, gamma); FeAdd(C, gamma, gamma, gamma);
  FeSub(C, t, t, R.X); FeMul(C, R.Y, alpha, t); FeSub(C, R.Y, R.Y, gamma);
end;

procedure PtAdd(const C: TCtx; out R: TPt; const A, B: TPt);
var z1z1, z2z2, u1, u2, s1, s2, h, i, j, rr, v, t: TFe;
begin
  FeMul(C, z1z1, A.Z, A.Z); FeMul(C, z2z2, B.Z, B.Z);
  FeMul(C, u1, A.X, z2z2); FeMul(C, u2, B.X, z1z1);
  FeMul(C, s1, A.Y, B.Z); FeMul(C, s1, s1, z2z2);
  FeMul(C, s2, B.Y, A.Z); FeMul(C, s2, s2, z1z1);
  FeSub(C, h, u2, u1);
  FeSub(C, rr, s2, s1); FeAdd(C, rr, rr, rr);
  FeAdd(C, t, h, h); FeMul(C, i, t, t);
  FeMul(C, j, h, i);
  FeMul(C, v, u1, i);
  FeMul(C, R.X, rr, rr); FeSub(C, R.X, R.X, j); FeAdd(C, t, v, v); FeSub(C, R.X, R.X, t);
  FeSub(C, t, v, R.X); FeMul(C, R.Y, rr, t); FeMul(C, t, s1, j); FeAdd(C, t, t, t); FeSub(C, R.Y, R.Y, t);
  FeAdd(C, t, A.Z, B.Z); FeMul(C, t, t, t); FeSub(C, t, t, z1z1); FeSub(C, t, t, z2z2); FeMul(C, R.Z, t, h);
end;

// K' = k + n (bit NBits is always 1) - ladder from the next bit down
procedure ScalarMul(const C: TCtx; const K: TBig; const X, Y: TFe; out AX, AY: TFe);
var r0, r1, t: TPt; i: Integer; bit: UInt32; zi, zi2: TFe;
begin
  r0.X := X; r0.Y := Y; r0.Z := C.OneM;
  PtDouble(C, r1, r0);
  for i := C.NBits - 1 downto 0 do
  begin
    bit := BigBit(K, i);
    FeCSwap(C, r0.X, r1.X, bit); FeCSwap(C, r0.Y, r1.Y, bit); FeCSwap(C, r0.Z, r1.Z, bit);
    PtAdd(C, t, r0, r1);
    PtDouble(C, r0, r0);
    r1 := t;
    FeCSwap(C, r0.X, r1.X, bit); FeCSwap(C, r0.Y, r1.Y, bit); FeCSwap(C, r0.Z, r1.Z, bit);
  end;
  FeInv(C, zi, r0.Z);
  FeMul(C, zi2, zi, zi);
  FeMul(C, AX, r0.X, zi2);
  FeMul(C, zi2, zi2, zi);
  FeMul(C, AY, r0.Y, zi2);
end;

function Extend(const C: TCtx; const Priv: TBytes): TBig;
begin
  Result := BigAdd(BigFromBytes(Priv), C.N);
  if BigBit(Result, C.NBits) <> 1 then
    raise Exception.Create('XTls ECDH: scalar out of range');
end;

function FromMont(const C: TCtx; const A: TFe): TFe;
var one: TFe;
begin
  FillChar(one, SizeOf(one), 0); one[0] := 1;
  FeMul(C, Result, A, one);
end;

function EcdhPublicOf(Curve: TEcdhCurve; const Priv: TBytes): TBytes;
var C: TCtx; ax, ay: TFe;
begin
  C := Ctx(Curve);
  ScalarMul(C, Extend(C, Priv), C.GX, C.GY, ax, ay);
  Result := Concat(TBytes.Create(4), BigToBytes(FeToBig(C, FromMont(C, ax)), C.Len));
  Result := Concat(Result, BigToBytes(FeToBig(C, FromMont(C, ay)), C.Len));
end;

procedure EcdhKeyPair(Curve: TEcdhCurve; out Priv, Pub: TBytes);
var C: TCtx; k: TBig;
begin
  C := Ctx(Curve);
  repeat
    Priv := RandomBytes(C.Len);
    if Curve = ecdhP521 then Priv[0] := Priv[0] and 1;        // 521 bits
    k := BigFromBytes(Priv);
  until (BigCmp(k, C.N) < 0) and (BigBits(k) > C.NBits - 32);   // then k + n has bit NBits set
  Pub := EcdhPublicOf(Curve, Priv);
end;

function EcdhShared(Curve: TEcdhCurve; const Priv, PeerPub: TBytes; out Secret: TBytes): Boolean;
var C: TCtx; qx, qy: TBig; mx, my, l, r, t, ax, ay, fx: TFe;
begin
  Result := False; Secret := nil;
  C := Ctx(Curve);
  if (Length(PeerPub) <> 1 + 2 * C.Len) or (PeerPub[0] <> 4) then Exit;
  qx := BigFromBytes(Copy(PeerPub, 1, C.Len));
  qy := BigFromBytes(Copy(PeerPub, 1 + C.Len, C.Len));
  if (BigCmp(qx, FeToBig(C, C.P)) >= 0) or (BigCmp(qy, FeToBig(C, C.P)) >= 0) then Exit;
  FeFromBig(C, t, qx); FeMul(C, mx, t, C.R2);
  FeFromBig(C, t, qy); FeMul(C, my, t, C.R2);
  // y^2 = x^3 - 3x + b (public point - the check need not be constant time)
  FeMul(C, l, my, my);
  FeMul(C, r, mx, mx); FeMul(C, r, r, mx);
  FeAdd(C, t, mx, mx); FeAdd(C, t, t, mx);
  FeSub(C, r, r, t); FeAdd(C, r, r, C.BM);
  if not FeEq(C, l, r) then Exit;
  ScalarMul(C, Extend(C, Priv), mx, my, ax, ay);
  fx := FromMont(C, ax);
  if Length(FeToBig(C, fx)) = 0 then Exit;
  Secret := BigToBytes(FeToBig(C, fx), C.Len);
  Result := True;
end;

var cv: TEcdhCurve;
initialization
  for cv := Low(TEcdhCurve) to High(TEcdhCurve) do InitCurve(cv);
end.
