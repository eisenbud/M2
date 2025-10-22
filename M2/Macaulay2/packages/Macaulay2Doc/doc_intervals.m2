doc ///
  Key
    left
  Headline
    left endpoint of an interval
  Usage
    x = left I
  Inputs
    I:RRi
  Outputs
    x:RR
  Description
    Text
      Returns the left endpoint of the input interval.
  SeeAlso
    right
    midpoint
    diameter
///

doc ///
  Key
    right
Headline
    right endpoint of an interval
Usage
    x = right I
Inputs
    I:RRi
Outputs
    x:RR
Description
  Text
    Returns the right endpoint of the input interval.
SeeAlso
    left
    midpoint
    diameter
///

doc ///
Key
    midpoint
Headline
    midpoint of an interval
Usage
    x = midpoint I
Inputs
    I:{RRi,CCi}
Outputs
    x:{RR,CC}
Description
  Text
    Returns the midpoint (the average of the endpoints) of the input interval.
  Example
    interval(2,4)
    midpoint oo
  Text
    For complex intervals, the center of the rectangle in the complex
    plane is returned.
  Example
    interval(2 + 3*ii, 4 + 7*ii)
    midpoint oo
SeeAlso
    left
    right
    diameter
///

doc ///
Key
    diameter
    (diameter, CCi)
    (diameter, RRi)
Headline
    diameter of an interval
Usage
    x = diameter I
Inputs
    I:{RRi, CCi}
Outputs
    x:RR
Description
  Text
    Returns the diameter (the difference between the endpoints) of the input interval.
  Example
    interval (2, 7)
    diameter oo
  Text
    For a complex interval, the length of the diagonal in the complex
    plane is returned.
  Example
    interval (0, 3 + 4*ii)
    diameter oo
SeeAlso
    left
    right
    midpoint
///

doc ///
Key
    (intersect, RRi)
    (intersect, RRi, RRi)
    [(intersect, RRi), Precision]
    [(intersect, RRi, RRi), Precision]
Headline
    intersection of input intervals
Usage
    J = intersect(I,...)
    J = intersect(I,...,Precision => prec)
Inputs
    I:RRi
    Precision => ZZ
        specifies the desired precision of the output, a value of {\tt -1} uses the minimum precision of the inputs.
Outputs
    J:RRi
Description
  Text
    Returns the intersection of any number of input intervals.
SeeAlso
    intersect
///

doc ///
Key
    (isMember, QQ, CCi)
    (isMember, RR, CCi)
    (isMember, ZZ, CCi)
    (isMember, CC, CCi)
    (isMember, QQ, RRi)
    (isMember, ZZ, RRi)
    (isMember, RR, RRi)
Headline
    membership test in an interval
Usage
    isMember(x,I)
Inputs
    x:{QQ,ZZ,RR,CC}
    I:CCi
Outputs
    :Boolean
Description
  Text
    Returns true if the input number is in the interval.
SeeAlso
    isEmpty
///

doc ///
Key
    (isEmpty, RRi)
    (isEmpty, CCi)
Headline
    empty test for an interval
Usage
    x = isEmpty(I)
Inputs
    I:RRi
Outputs
    x:Boolean
Description
  Text
    Returns true if the input interval is empty, i.e., the left endpoint is to the right of the right endpoint.
SeeAlso
    isMember
///

doc ///
Key
    (isSubset, CCi, CCi)
    (isSubset, RRi, RRi)
    (isSubset, RRi, CCi)
    (isSubset, CCi, RRi)
Headline
    subset test for intervals
Usage
    x = isSubset(I,J)
Inputs
    I:CCi
    J:CCi
Outputs
    x:Boolean
Description
  Text
    Returns true if interval I is a subset of interval J.
SeeAlso
    isMember
///

undocumented{(isReal, CCi), (span, CCi), (span,RRi), (span, QQ), (span, RR), (span, ZZ)}

doc ///
Key
    span
Headline
    construct smallest interval
Description
  Text
    Returns the smallest interval containing the inputs (which can include intervals).  Typically, the returned interval is not empty.  See @TO (span, Sequence)@ and @TO (span, List)@
SeeAlso
    interval
    (span, Sequence)
    (span, List)
    toRRi
    toCCi
///

doc ///
Key
    (span, List)
    [(span,List),Precision]
Headline
    construct smallest interval
Usage
    I = span(L)
    I = span(L,Precision => prec)
Inputs
    L:List
        containing @TO Number@ (including @TO CCi@)
    Precision => ZZ
        specifies the desired precision of the output, a value of {\tt -1} uses the minimum precision of the inputs.
Outputs
    I:RRi
	when input List has only real numbers or intervals
    I:CCi
Description
  Text
    Returns the smallest interval containing the inputs (which can include intervals).  Typically, the returned interval is not empty.
SeeAlso
    interval
    (span, Sequence)
    toRRi
    toCCi
///

doc ///
Key
    (span, Sequence)
    [(span,Sequence),Precision]
Headline
    construct smallest interval
Usage
    I = span(S)
    I = span(S,Precision => prec)
Inputs
    S:Sequence
        containing @TO Number@ (including @TO CCi@)
    Precision => ZZ
        specifies the desired precision of the output, a value of {\tt -1} uses the minimum precision of the inputs.
Outputs
    I:RRi
	when input List has only real numbers or intervals
    I:CCi
Description
  Text
    Returns the smallest interval containing the inputs (which can include intervals).  Typically, the returned interval is not empty.
SeeAlso
    interval
    (span, List)
    toRRi
    toCCi
///

doc ///
Key
    interval
    (interval,Array)
    (interval,CC)
    (interval,CC,CC)
    (interval,CC,Number)
    (interval,CCi)
    (interval,Number,CC)
    (interval,QQ)
    (interval,QQ,QQ)
    (interval,QQ,RR)
    (interval,QQ,RRi)
    (interval,QQ,ZZ)
    (interval,RR)
    (interval,RR,QQ)
    (interval,RR,RR)
    (interval,RR,RRi)
    (interval,RR,ZZ)
    (interval,RRi)
    (interval,RRi,QQ)
    (interval,RRi,RR)
    (interval,RRi,RRi)
    (interval,RRi,ZZ)
    (interval,ZZ)
    (interval,ZZ,QQ)
    (interval,ZZ,RR)
    (interval,ZZ,RRi)
    (interval,ZZ,ZZ)
    [interval,Precision]
Headline
    construct an interval
Usage
    I = interval(n)
    I = interval(l,r)
    I = interval([l,r])
    I = interval(n,Precition => prec)
    I = interval(l,r,Precition => prec)
    I = interval([l,r],Precition => prec)
Inputs
    n:Number
    l:Number
    r:Number
    Precision => ZZ
        specifies the desired precision of the output, a value of {\tt -1} uses the @TO "defaultPrecision"@ or the minimum precisions of the inputs.
Outputs
    I:RRi
Description
  Text
    If given one argument, returns a real or complex interval as small as possible containing {\tt n}.
  Example
    interval 3
    interval(2 + 5*ii)
  Text
    If given two real arguments (or an array with two entries), the interval
    from {\tt l} to {\tt r}.  Note that if {\tt l} is to the right of
    {\tt r}, the constructed interval is empty.
  Example
    interval(2, 3)
    interval(5, 4)
    interval [7, 8]
  Text
    If given two arguments, at least one of which is a complex number,
    then the rectangle in the complex plane containing the two
    arguments is returned.
  Example
    interval(2 + 3*ii, 5)
  Text
    If given two arguments, at least one of which is a real interval,
    then the first argument gives the real part and the second argument
    the imaginary part of a complex interval.
  Example
    interval(interval(3, 4), interval(5, 6))
  Text
    The @M2CODE "Precision"@ option sets the precision of the output.
  Example
    interval(Precision => 100, 5)
SeeAlso
    (span, List)
    (span, Sequence)
    toRRi
///

doc ///
Key
    toRRi
Headline
    construct an interval
Usage
    I = toRRi(n)
    I = toRRi(l,r)
    I = toRRi(prec,l,r)
Inputs
    n:Number
    l:Number
    r:Number
    prec:ZZ
Outputs
    I:RRi
Description
  Text
    Returns an interval as small as possible containing {\tt n} or from {\tt l} to {\tt r}.  Note that if {\tt l} is to the right of {\tt r}, the constructed interval is empty.  This is a more low-level function and @TO interval@ or span should be used instead.
SeeAlso
    (span, List)
    (span, Sequence)
    interval
///

doc ///
Key
    numericInterval
    (numericInterval, Constant)
    (numericInterval, ZZ, Constant)
Headline
    convert a constant to an interval
Usage
    I = numericInterval(c)
    I = numericInterval(prec,c)
Inputs
    c:Constant
    prec:ZZ
Outputs
    I:RRi
Description
  Text
    Constructs an interval containing {\tt c} of either the @TO "defaultPrecision"@ or precision {\tt prec}
SeeAlso
    (span, List)
    (span, Sequence)
    interval
    toRRi
///

doc ///
Key
    toCCi
Headline
    construct an interval
Usage
    I = toCCi(n)
    I = toCCi(re,im)
    I = toCCi(prec,re,im)
Inputs
    n:CC
    re:RRi
    im:RRi
    prec:ZZ
Outputs
    I:CCi
Description
  Text
    Returns an interval as small as possible containing {\tt n} or from {\tt l} to {\tt r}.  Note that if {\tt l} is to the right of {\tt r}, the constructed interval is empty.  This is a more low-level function and @TO interval@ or span should be used instead.
SeeAlso
    (span, List)
    (span, Sequence)
    interval
///

