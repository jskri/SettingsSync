---- MODULE MC ----
EXTENDS SettingsSync, TLC

\* CONSTANT definitions @modelParameterConstants:0MinDate
const_1720969013957200000 == 
0
----

\* CONSTANT definitions @modelParameterConstants:1Date
const_1720969013957201000 == 
0..4
----

\* CONSTANT definitions @modelParameterConstants:2StampValue
const_1720969013957202000 == 
Value \X Date
----

\* CONSTANT definitions @modelParameterConstants:3Attr
const_1720969013957203000 == 
{"attr_a", "attr_b"}
----

\* CONSTANT definitions @modelParameterConstants:4DefaultValue
const_1720969013957204000 == 
0
----

\* CONSTANT definitions @modelParameterConstants:6InitialNow
const_1720969013957205000 == 
0
----

\* CONSTANT definitions @modelParameterConstants:7Value
const_1720969013957206000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:8DefaultConf
const_1720969013957207000 == 
[t \in Attr |->
  IF t = "attr_a" THEN <<0, 0>>
  ELSE None]
----

\* CONSTANT definitions @modelParameterConstants:9dateLte(a, b)
const_1720969013957208000(a, b) == 
a <= b
----

\* CONSTANT definitions @modelParameterConstants:10MkStampValue(v, d)
const_1720969013957209000(v, d) == 
<<v, d>>
----

\* CONSTANT definitions @modelParameterConstants:11DateOf(vd)
const_1720969013957210000(vd) == 
vd[2]
----

\* CONSTANT definitions @modelParameterConstants:12NextDate(d)
const_1720969013957211000(d) == 
IF d < 4 THEN d + 1 ELSE d
----

=============================================================================
