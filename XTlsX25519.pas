// XTls - X25519 (RFC 7748), after TweetNaCl (Bernstein et al., public domain).
// Field element: 16 limbs of 16 bits in Int64; Montgomery ladder with
// branch-free conditional swaps (constant time). License: MIT.
unit XTlsX25519;

{$mode objfpc}{$H+}{$Q-}{$R-}

interface

uses
  SysUtils;

// Q = scalar * point (32 bytes each).
function X25519(const Scalar, Point: TBytes): TBytes;
// Public key = scalar * 9
function X25519Base(const Scalar: TBytes): TBytes;

implementation

type
  TGf = array[0..15] of Int64;

const
  C121665: TGf = ($DB41, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);

procedure Car(var o: TGf);
var i: Integer; c: Int64;
begin
  for i := 0 to 15 do
  begin
    o[i] := o[i] + (Int64(1) shl 16);
    c := SarInt64(o[i], 16);
    if i < 15 then o[i + 1] := o[i + 1] + c - 1
    else o[0] := o[0] + 38 * (c - 1);          // c-1 + 37*(c-1)
    o[i] := o[i] - (c shl 16);
  end;
end;

// swap p and q when b = 1 (branch-free)
procedure Sel(var p, q: TGf; b: Integer);
var i: Integer; t, c: Int64;
begin
  c := not (Int64(b) - 1);
  for i := 0 to 15 do
  begin
    t := c and (p[i] xor q[i]);
    p[i] := p[i] xor t;
    q[i] := q[i] xor t;
  end;
end;

procedure Pack(out o: TBytes; const n: TGf);
var i, j: Integer; b: Int64; m, t: TGf;
begin
  t := n;
  Car(t); Car(t); Car(t);
  for j := 0 to 1 do
  begin
    m[0] := t[0] - $FFED;
    for i := 1 to 14 do
    begin
      m[i] := t[i] - $FFFF - ((m[i - 1] shr 16) and 1);
      m[i - 1] := m[i - 1] and $FFFF;
    end;
    m[15] := t[15] - $7FFF - ((m[14] shr 16) and 1);
    b := (m[15] shr 16) and 1;
    m[14] := m[14] and $FFFF;
    Sel(t, m, 1 - b);
  end;
  SetLength(o, 32);
  for i := 0 to 15 do
  begin
    o[2 * i] := Byte(t[i] and $FF);
    o[2 * i + 1] := Byte((t[i] shr 8) and $FF);
  end;
end;

procedure Unpack(out o: TGf; const n: TBytes);
var i: Integer;
begin
  for i := 0 to 15 do o[i] := n[2 * i] + (Int64(n[2 * i + 1]) shl 8);
  o[15] := o[15] and $7FFF;
end;

procedure FAdd(out o: TGf; const a, b: TGf);
var i: Integer;
begin for i := 0 to 15 do o[i] := a[i] + b[i]; end;

procedure FSub(out o: TGf; const a, b: TGf);
var i: Integer;
begin for i := 0 to 15 do o[i] := a[i] - b[i]; end;

procedure FMul(out o: TGf; const a, b: TGf);
var i, j: Integer; t: array[0..30] of Int64;
begin
  for i := 0 to 30 do t[i] := 0;
  for i := 0 to 15 do
    for j := 0 to 15 do
      t[i + j] := t[i + j] + a[i] * b[j];
  for i := 0 to 14 do t[i] := t[i] + 38 * t[i + 16];
  for i := 0 to 15 do o[i] := t[i];
  Car(o); Car(o);
end;

procedure FInv(out o: TGf; const inp: TGf);
var c: TGf; a: Integer;
begin
  c := inp;
  for a := 253 downto 0 do
  begin
    FMul(c, c, c);
    if (a <> 2) and (a <> 4) then FMul(c, c, inp);
  end;
  o := c;
end;

function X25519(const Scalar, Point: TBytes): TBytes;
var
  z: array[0..31] of Byte;
  x, a, b, c, d, e, f, t: TGf;
  i, r: Integer;
begin
  if (Length(Scalar) <> 32) or (Length(Point) <> 32) then
    raise Exception.Create('XTls X25519: invalid length');
  Move(Scalar[0], z[0], 32);
  z[31] := (z[31] and 127) or 64;
  z[0] := z[0] and 248;
  Unpack(x, Point);
  for i := 0 to 15 do begin b[i] := x[i]; a[i] := 0; c[i] := 0; d[i] := 0; end;
  a[0] := 1; d[0] := 1;
  for i := 254 downto 0 do
  begin
    r := (z[i shr 3] shr (i and 7)) and 1;
    Sel(a, b, r); Sel(c, d, r);
    FAdd(e, a, c); FSub(a, a, c); FAdd(c, b, d); FSub(b, b, d);
    FMul(d, e, e); FMul(f, a, a);
    FMul(a, c, a); FMul(c, b, e);
    FAdd(e, a, c); FSub(a, a, c);
    FMul(b, a, a); FSub(c, d, f);
    FMul(a, c, C121665); FAdd(a, a, d);
    FMul(c, c, a); FMul(a, d, f);          // z2 = E*(AA + a24*E); x2 = AA*BB
    FMul(d, b, x); FMul(b, e, e);
    Sel(a, b, r); Sel(c, d, r);
  end;
  FInv(t, c);
  FMul(a, a, t);
  Pack(Result, a);
  FillChar(z, SizeOf(z), 0);
end;

function X25519Base(const Scalar: TBytes): TBytes;
var nine: TBytes;
begin
  SetLength(nine, 32);
  FillChar(nine[0], 32, 0);
  nine[0] := 9;
  Result := X25519(Scalar, nine);
end;

end.
