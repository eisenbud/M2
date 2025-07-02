needs "methods.m2"
needs "shared.m2"
needs "reals.m2"

interval = method(Options => {Precision => -1})

for A in {ZZ,QQ,RR} do
interval A := opts -> N -> (
    if opts.Precision < 0 then toRRi(N)
    else toRRi(opts.Precision,N,N))
interval(RRi) := opts -> A -> A
interval(CCi) := opts -> A -> toCCi A

for A in {ZZ,QQ,RR} do
for B in {ZZ,QQ,RR} do
interval(A,B) := opts -> (N,M) -> (
    if opts.Precision < 0 then toRRi(N,M)
    else toRRi(opts.Precision,N,M))

interval(RRi,RRi) := opts -> (N,M) -> (
    if opts.Precision < 0 then toCCi(N,M)
    else toCCi(opts.Precision,N,M))

interval(CC) := opts -> A -> toCCi A

for A in {ZZ,QQ,RR} do
interval(CC,A) := opts -> (N,M) -> (
    if opts.Precision < 0 then toCCi(interval(realPart N, M), interval imaginaryPart N)
    else toCCi(opts.Precision, interval(realPart N, M), interval imaginaryPart N))
for A in {ZZ,QQ,RR} do
interval(A,CC) := opts -> (N,M) -> (
    if opts.Precision < 0 then toCCi(interval(N, realPart M), interval imaginaryPart M)
    else toCCi(opts.Precision, interval(realPart N, M), interval imaginaryPart N))
for A in {ZZ,QQ,RR} do
interval(CC,CC) := opts -> (N,M) -> (
    if opts.Precision < 0 then toCCi(interval(realPart N, realPart M), interval (imaginaryPart N, imaginaryPart M))
    else toCCi(opts.Precision, interval(realPart N, M), interval imaginaryPart N))


interval(Array) := opts -> A -> (
    if (length(A) == 0) or (length(A)>2) then error("expected length 2")
    else if length(A) == 1 then interval(opts,A_0)
    else interval(opts,A_0,A_1))    

spanRRi = method(Options => {Precision => -1})

for A in {ZZ,QQ,RR,RRi} do
spanRRi(A) := opts -> (M) -> (
    if opts.Precision < 0 then toRRi(M)
    else toRRi(opts.Precision,M))

for A in {ZZ,QQ,RR} do
for B in {ZZ,QQ,RR} do
spanRRi(A,B) := opts -> (N,M) -> (
    if opts.Precision < 0 then toRRi(min(M,N),max(M,N))
    else toRRi(opts.Precision,min(M,N),max(M,N)))

for A in {ZZ,QQ,RR} do (
spanRRi(RRi,A) := opts -> (N,M) -> (
    if isEmpty(N) then interval(opts,M)
    else if opts.Precision < 0 then toRRi(min(left N,M),max(right N,M))
    else toRRi(opts.Precision,min(left N,M),max(right N,M)));
spanRRi(A,RRi) := opts -> (N,M) -> span(opts,M,N))

spanRRi(RRi,RRi) := opts -> (N,M) -> (
    if isEmpty(N) then interval(opts,left M, right M)
    else if isEmpty(M) then interval(opts, left N, right N)
    else if opts.Precision < 0 then toRRi(min(left N,left M),max(right N,right M))
    else toRRi(opts.Precision,min(left N,left M),max(right N,right M)))

spanCCi = method(Options => {Precision => -1})

--for A in {ZZ,QQ,RR,RRi} do
--for B in {ZZ,QQ,RR,RRi} do
--spanCCi(A,B) := opts -> (N,M) -> (
--    toCCi(spanRRi(N,M), interval 0)
--    )

for A in {ZZ,QQ,RR,RRi} do (
spanCCi(CC,A) := opts -> (N,M) -> (
    if opts.Precision < 0 then toCCi(spanRRi(realPart N,M),toRRi imaginaryPart N)
    else toCCi(opts.Precision,spanRRi(realPart N,M),toRRi imaginaryPart N));--toRRi(opts.Precision,min(left N,M),max(right N,M)));
spanCCi(A,CC) := opts -> (N,M) -> spanCCi(opts,M,N);
spanCCi(CCi,A) := opts -> (N,M) -> (
    if opts.Precision < 0 then toCCi(spanRRi(realPart N,M),imaginaryPart N)
    else toCCi(opts.Precision,spanRRi(realPart N,M),imaginaryPart N));--toRRi(opts.Precision,min(left N,M),max(right N,M)));
spanCCi(A,CCi) := opts -> (N,M) -> spanCCi(opts,M,N))

spanCCi(CC,CC) := opts -> (N,M) -> (
    if opts.Precision < 0 then toCCi(spanRRi(realPart N,realPart M),spanRRi(imaginaryPart N, imaginaryPart M)))
spanCCi(CC,CCi) := opts -> (N,M) -> (
    if opts.Precision < 0 then toCCi(spanRRi(realPart N,realPart M),spanRRi(imaginaryPart N, imaginaryPart M)))
spanCCi(CCi,CC) := opts -> (N,M) -> spanCCi(opts,M,N)
spanCCi(CCi,CCi) := opts -> (N,M) -> (
    if opts.Precision < 0 then toCCi(spanRRi(realPart N,realPart M),spanRRi(imaginaryPart N, imaginaryPart M)))
    
spanner = method(Options => {Precision => -1})

for A in {ZZ,QQ,RR,RRi} do
for B in {ZZ,QQ,RR,RRi} do
spanner(A,B) := opts -> (N,M) -> (spanRRi(N,M))

for A in {ZZ,QQ,RR,RRi,CC,CCi} do
for B in {CC,CCi} do
spanner(A,B) := opts -> (N,M) -> (spanCCi(N,M))

for A in {CC,CCi} do
for B in {ZZ,QQ,RR,RRi} do
spanner(A,B) := opts -> (N,M) -> (spanCCi(N,M))

span = method(Dispatch => Thing, Options => true)

span ZZ := span QQ := span RR := {Precision => -1} >> opts -> N -> interval(N,opts)

span RRi := {Precision => -1} >> opts -> N -> interval(left N,right N,opts)

span CC := {Precision => -1} >> opts -> N -> interval(realPart N,imaginaryPart N,opts)

span CCi := {Precision => -1} >> opts -> N -> interval(realPart N,imaginaryPart N,opts)

span List := span Sequence := {Precision => -1} >> opts -> L -> fold(L, (N, M) -> spanner(N, M, opts))

for A in {ZZ,QQ,RR} do
isMember(A,RRi) := (N,M) -> subsetRRi(N,M);

isSubset(RRi,RRi) := (N,M) -> subsetRRi(N,M);

-- intersect is an associative binary method, so it works on arbitrary lists and sequences
intersect RRi       := RRi => { Precision => -1 } >> opts -> identity
intersect(RRi, RRi) := RRi => { Precision => -1 } >> opts -> (N, M) -> (
    if opts.Precision < 0 then intersectRRi(N,M)
    else intersectRRi(opts.Precision,N,M))

isEmpty RRi := Boolean => isEmptyRRi
isEmpty CCi := x -> isEmptyRRi realPart x or isEmptyRRi imaginaryPart x

toExternalString RRi := x -> "interval" | toExternalString (left x, right x)
toExternalString CCi := x -> "interval" | toExternalString (left realPart x+(left imaginaryPart x)*ii,right realPart x+(right imaginaryPart x)*ii)
