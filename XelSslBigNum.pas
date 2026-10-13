// XelSSL - minimal big natural number arithmetic (for RSA/ECDSA verification).
// 32-bit little-endian limbs; division: Knuth's algorithm D (after "Hacker's
// Delight", divmnu64). Operations are NOT constant time - used only on
// public data (signatures, public keys). License: MIT.
unit XelSslBigNum;

{$mode objfpc}{$H+}{$Q-}{$R-}

interface

uses
  SysUtils;

type
  TBig = array of UInt32;        // normalized: no trailing zero limbs; 0 = []

function BigFromBytes(const B: TBytes): TBig;          // big-endian
function BigFromHex(const S: string): TBig;
function BigFromInt(V: UInt32): TBig;
function BigToBytes(const A: TBig; Len: Integer = 0): TBytes;   // Len=0: minimal length
function BigIsZero(const A: TBig): Boolean; inline;
function BigCmp(const A, B: TBig): Integer;
function BigBits(const A: TBig): Integer;
function BigBit(const A: TBig; I: Integer): Integer; inline;
function BigAdd(const A, B: TBig): TBig;
function BigSub(const A, B: TBig): TBig;               // requires A >= B
function BigMul(const A, B: TBig): TBig;
procedure BigDivMod(const U, V: TBig; out Q, R: TBig);
function BigMod(const A, M: TBig): TBig;
function BigShr(const A: TBig; N: Integer): TBig;
function BigModAdd(const A, B, M: TBig): TBig;
function BigModSub(const A, B, M: TBig): TBig;
function BigModMul(const A, B, M: TBig): TBig;
function BigModExp(const Base, Exp, M: TBig): TBig;
function BigModInvPrime(const A, P: TBig): TBig;       // A^(P-2) mod P

implementation

procedure Norm(var A: TBig); inline;
var n: Integer;
begin
  n := Length(A);
  while (n > 0) and (A[n - 1] = 0) do Dec(n);
  SetLength(A, n);
end;

function BigFromBytes(const B: TBytes): TBig;
var i, n: Integer;
begin
  n := (Length(B) + 3) div 4;
  SetLength(Result, n);
  for i := 0 to n - 1 do Result[i] := 0;
  for i := 0 to High(B) do
    Result[(Length(B) - 1 - i) div 4] := Result[(Length(B) - 1 - i) div 4] or
      (UInt32(B[i]) shl (8 * ((Length(B) - 1 - i) mod 4)));
  Norm(Result);
end;

function BigFromHex(const S: string): TBig;
var t: string; i: Integer; b: TBytes;
begin
  t := '';
  for i := 1 to Length(S) do if S[i] in ['0'..'9', 'a'..'f', 'A'..'F'] then t := t + S[i];
  if Odd(Length(t)) then t := '0' + t;
  SetLength(b, Length(t) div 2);
  for i := 0 to High(b) do b[i] := StrToInt('$' + Copy(t, i * 2 + 1, 2));
  Result := BigFromBytes(b);
end;

function BigFromInt(V: UInt32): TBig;
begin
  if V = 0 then Result := nil
  else begin SetLength(Result, 1); Result[0] := V; end;
end;

function BigToBytes(const A: TBig; Len: Integer): TBytes;
var i, nb: Integer;
begin
  nb := (BigBits(A) + 7) div 8;
  if Len = 0 then Len := nb;
  if nb > Len then raise Exception.Create('XelSSL BigNum: number too long');
  SetLength(Result, Len);
  FillChar(Result[0], Len, 0);
  for i := 0 to nb - 1 do
    Result[Len - 1 - i] := Byte(A[i div 4] shr (8 * (i mod 4)));
end;

function BigIsZero(const A: TBig): Boolean;
begin Result := Length(A) = 0; end;

function BigCmp(const A, B: TBig): Integer;
var i: Integer;
begin
  if Length(A) <> Length(B) then
  begin
    if Length(A) > Length(B) then Exit(1) else Exit(-1);
  end;
  for i := High(A) downto 0 do
    if A[i] <> B[i] then
    begin
      if A[i] > B[i] then Exit(1) else Exit(-1);
    end;
  Result := 0;
end;

function BigBits(const A: TBig): Integer;
var t: UInt32;
begin
  if Length(A) = 0 then Exit(0);
  Result := (Length(A) - 1) * 32;
  t := A[High(A)];
  while t <> 0 do begin Inc(Result); t := t shr 1; end;
end;

function BigBit(const A: TBig; I: Integer): Integer;
begin
  if I shr 5 >= Length(A) then Result := 0
  else Result := (A[I shr 5] shr (I and 31)) and 1;
end;

function BigAdd(const A, B: TBig): TBig;
var i, n: Integer; c: UInt64;
begin
  n := Length(A); if Length(B) > n then n := Length(B);
  SetLength(Result, n + 1);
  c := 0;
  for i := 0 to n - 1 do
  begin
    if i < Length(A) then c := c + A[i];
    if i < Length(B) then c := c + B[i];
    Result[i] := UInt32(c);
    c := c shr 32;
  end;
  Result[n] := UInt32(c);
  Norm(Result);
end;

function BigSub(const A, B: TBig): TBig;
var i: Integer; t: Int64; borrow: Int64;
begin
  SetLength(Result, Length(A));
  borrow := 0;
  for i := 0 to High(A) do
  begin
    t := Int64(A[i]) - borrow;
    if i < Length(B) then t := t - B[i];
    if t < 0 then begin t := t + (Int64(1) shl 32); borrow := 1; end else borrow := 0;
    Result[i] := UInt32(t);
  end;
  if borrow <> 0 then raise Exception.Create('XelSSL BigNum: negative subtraction result');
  Norm(Result);
end;

function BigMul(const A, B: TBig): TBig;
var i, j: Integer; c: UInt64;
begin
  if (Length(A) = 0) or (Length(B) = 0) then Exit(nil);
  SetLength(Result, Length(A) + Length(B));
  for i := 0 to High(Result) do Result[i] := 0;
  for i := 0 to High(A) do
  begin
    c := 0;
    for j := 0 to High(B) do
    begin
      c := c + UInt64(A[i]) * B[j] + Result[i + j];
      Result[i + j] := UInt32(c);
      c := c shr 32;
    end;
    Result[i + Length(B)] := UInt32(c);
  end;
  Norm(Result);
end;

function Nlz(X: UInt32): Integer;
begin
  Result := 0;
  if X = 0 then Exit(32);
  while (X and $80000000) = 0 do begin Inc(Result); X := X shl 1; end;
end;

procedure BigDivMod(const U, V: TBig; out Q, R: TBig);
const B = UInt64($100000000);
var
  m, n, s, i, j: Integer;
  un, vn: array of UInt32;
  qhat, rhat, p, rem: UInt64; t, k: Int64;
begin
  if Length(V) = 0 then raise EDivByZero.Create('XelSSL BigNum: division by zero');
  if BigCmp(U, V) < 0 then begin Q := nil; R := Copy(U); Exit; end;
  n := Length(V); m := Length(U) - n;
  SetLength(Q, m + 1);
  if n = 1 then
  begin
    rem := 0;
    for j := High(U) downto 0 do
    begin
      rem := (rem shl 32) or U[j];
      Q[j] := UInt32(rem div V[0]);
      rem := rem mod V[0];
    end;
    Norm(Q);
    R := BigFromInt(UInt32(rem));
    Exit;
  end;
  s := Nlz(V[n - 1]);
  SetLength(vn, n);
  for i := n - 1 downto 1 do
    if s > 0 then vn[i] := (V[i] shl s) or (V[i - 1] shr (32 - s)) else vn[i] := V[i];
  vn[0] := V[0] shl s;
  SetLength(un, m + n + 1);
  if s > 0 then un[m + n] := U[m + n - 1] shr (32 - s) else un[m + n] := 0;
  for i := m + n - 1 downto 1 do
    if s > 0 then un[i] := (U[i] shl s) or (U[i - 1] shr (32 - s)) else un[i] := U[i];
  un[0] := U[0] shl s;
  for j := m downto 0 do
  begin
    p := (UInt64(un[j + n]) shl 32) or un[j + n - 1];
    qhat := p div vn[n - 1];
    rhat := p mod vn[n - 1];
    while (qhat >= B) or (qhat * vn[n - 2] > (rhat shl 32) + un[j + n - 2]) do
    begin
      Dec(qhat);
      rhat := rhat + vn[n - 1];
      if rhat >= B then Break;
    end;
    k := 0;
    for i := 0 to n - 1 do
    begin
      p := qhat * vn[i];
      t := Int64(un[i + j]) - k - Int64(p and $FFFFFFFF);
      un[i + j] := UInt32(t);
      k := Int64(p shr 32) - SarInt64(t, 32);
    end;
    t := Int64(un[j + n]) - k;
    un[j + n] := UInt32(t);
    Q[j] := UInt32(qhat);
    if t < 0 then
    begin
      Q[j] := Q[j] - 1;
      k := 0;
      for i := 0 to n - 1 do
      begin
        t := Int64(un[i + j]) + vn[i] + k;
        un[i + j] := UInt32(t);
        k := t shr 32;
      end;
      un[j + n] := un[j + n] + UInt32(k);
    end;
  end;
  Norm(Q);
  SetLength(R, n);
  for i := 0 to n - 1 do
    if s > 0 then R[i] := (un[i] shr s) or (un[i + 1] shl (32 - s)) else R[i] := un[i];
  Norm(R);
end;

function BigMod(const A, M: TBig): TBig;
var q: TBig;
begin
  BigDivMod(A, M, q, Result);
end;

function BigShr(const A: TBig; N: Integer): TBig;
var w, b, i: Integer;
begin
  w := N shr 5; b := N and 31;
  if w >= Length(A) then Exit(nil);
  SetLength(Result, Length(A) - w);
  for i := 0 to High(Result) do
  begin
    Result[i] := A[i + w] shr b;
    if (b > 0) and (i + w + 1 < Length(A)) then Result[i] := Result[i] or (A[i + w + 1] shl (32 - b));
  end;
  Norm(Result);
end;

function BigModAdd(const A, B, M: TBig): TBig;
begin
  Result := BigAdd(A, B);
  if BigCmp(Result, M) >= 0 then Result := BigSub(Result, M);
end;

function BigModSub(const A, B, M: TBig): TBig;
begin
  if BigCmp(A, B) >= 0 then Result := BigSub(A, B)
  else Result := BigSub(BigAdd(A, M), B);
end;

function BigModMul(const A, B, M: TBig): TBig;
begin
  Result := BigMod(BigMul(A, B), M);
end;

function BigModExp(const Base, Exp, M: TBig): TBig;
var i: Integer; b: TBig;
begin
  Result := BigFromInt(1);
  b := BigMod(Base, M);
  for i := BigBits(Exp) - 1 downto 0 do
  begin
    Result := BigModMul(Result, Result, M);
    if BigBit(Exp, i) = 1 then Result := BigModMul(Result, b, M);
  end;
  Result := BigMod(Result, M);
end;

function BigModInvPrime(const A, P: TBig): TBig;
begin
  Result := BigModExp(A, BigSub(P, BigFromInt(2)), P);
end;

end.
