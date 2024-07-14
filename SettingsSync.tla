------------------------------ MODULE SettingsSync ------------------------------
EXTENDS Naturals, TLAPS

-----------------------------------------------------------------------------
(* Constants, general definitions, assumptions, variables *)

(* See also the assumptions below. *)
CONSTANTS
  Attr,               (* set of attributes *)
  Value,              (* set of values of attributes *)
  Date,               (* set of dates *)
  DefaultValue,       (* value element used in the default conf *)
  dateLte(_, _),      (* <= for dates. "Lte" means "less than or equal" *)
  MinDate,            (* date element that is the oldest *)
  NextDate(_),        (* successor of a date *)
  StampValue,         (* set of values paired with a timestamp (i.e. a date) *)
  None,               (* element different from any stamped value *)
  DefaultConf,        (* conf element whose attributes are timestamped at the min date *)
  DateOf(_),          (* date of a stamped value *)
  MkStampValue(_, _), (* constructor of stamped values *)
  InitialNow          (* initial value of now (see variables) *)

(* Optional stamped value
 * A stamped value is a value associated to a date.
 *)
OptStampValue == StampValue \union {None}

(* Configuration
 * A configuration is a function from attributes to optional stamped values.
 *)
Conf == [Attr -> OptStampValue]

(* Constraints on constants. *)
ASSUME Assumptions ==
  /\ DefaultConf \in Conf
  /\ \A t \in Attr :
       DefaultConf[t] /= None => DateOf(DefaultConf[t]) = MinDate
  /\ None \notin StampValue
  /\ \A a, b \in Date :
       /\ dateLte(a, b) \in BOOLEAN
       /\ dateLte(a, b) /\ dateLte(b, a) => a = b
  /\ \A a, b \in Date :
    \/ (  dateLte(a, b) /\ ~ dateLte(b, a)) (* a < b *)
    \/ (  dateLte(a, b) /\   dateLte(b, a)) (* a = b *)
    \/ (~ dateLte(a, b) /\   dateLte(b, a)) (* a > b *)
  /\ \A a \in Date :
       dateLte(a, a)
  /\ \A a, b, c \in Date :
       dateLte(a, b) /\ dateLte(b, c) => dateLte(a, c)
  /\ DefaultValue \in Value
  /\ MinDate \in Date
  /\ InitialNow \in Date
  /\ \A d \in Date : dateLte(MinDate, d)
  /\ \A s \in StampValue : DateOf(s) \in Date
  /\ \A d \in Date : NextDate(d) \in Date
  /\ \A d \in Date : dateLte(d, NextDate(d))
  /\ \A v \in Value, d \in Date :
       /\ MkStampValue(v, d) \in StampValue
       /\ DateOf(MkStampValue(v, d))  = d

(* `conf` is the (local) device configuration.
 * `reported` is the (remote) reported configuration.
 * `desired` is the (remote) desired configuration.
 * `now` is the current date.
 * `running` is true iff the device is running.
 * `connected` is true iff the device is connected to the network, i.e. online.
 *)
VARIABLES conf, reported, desired, now, running, connected
vars == <<conf, reported, desired, now, running, connected>>

-----------------------------------------------------------------------------
(* Order on optional stamped values *)

(* <= for optional stamped values.
 * Note: `None` is before (or equal to) any value.
 *)
OptStampValueLte(a, b) ==
  CASE a =  None /\ b =  None -> TRUE
    [] a =  None /\ b /= None -> TRUE
    [] a /= None /\ b =  None -> FALSE
    [] a /= None /\ b /= None -> dateLte(DateOf(a), DateOf(b))

LEMMA OptStampValueLteType ==
  \A a, b \in OptStampValue : OptStampValueLte(a, b) \in BOOLEAN
BY Assumptions, Zenon DEF OptStampValueLte, OptStampValue

LEMMA OptStampValueLteReflexive ==
  \A a \in OptStampValue : OptStampValueLte(a, a)
BY Assumptions, Zenon DEF OptStampValueLte, OptStampValue

LEMMA OptStampValueLteTransitive ==
  \A a, b, c \in OptStampValue :
    OptStampValueLte(a, b) /\ OptStampValueLte(b, c) =>
      OptStampValueLte(a, c)
<1> SUFFICES ASSUME NEW a \in OptStampValue, NEW b \in OptStampValue, NEW c \in OptStampValue,
                    OptStampValueLte(a, b) /\ OptStampValueLte(b, c)
             PROVE  OptStampValueLte(a, c)
  OBVIOUS
<1> QED
  BY Assumptions, Zenon DEF OptStampValueLte, OptStampValue

LEMMA OptStampValueLteAsymmetric ==
  \A a, b \in OptStampValue :
    ~ OptStampValueLte(a, b) => OptStampValueLte(b, a)
BY Assumptions, Zenon DEF OptStampValueLte, OptStampValue

LEMMA OptStampValueLteStrictOrdering ==
  /\ OptStampValueLteTransitive
  /\ \A a, b \in OptStampValue :
       \/ (  OptStampValueLte(a, b) /\ ~ OptStampValueLte(b, a)) (* a < b *)
       \/ (  OptStampValueLte(a, b) /\   OptStampValueLte(b, a)) (* a = b *)
       \/ (~ OptStampValueLte(a, b) /\   OptStampValueLte(b, a)) (* a > b *)
BY Assumptions, OptStampValueLteTransitive, Zenon
  DEF OptStampValueLte, OptStampValue

-----------------------------------------------------------------------------
(* Order on configurations *)

a \preceq b ==
  \A t \in Attr : OptStampValueLte(a[t], b[t])

LEMMA ConfLteReflexive ==
  \A a \in Conf : a \preceq a
BY OptStampValueLteReflexive DEF \preceq, Conf

LEMMA ConfLteTransitive ==
  \A a, b, c \in Conf : a \preceq b /\ b \preceq c => a \preceq c
BY OptStampValueLteTransitive DEF \preceq, Conf

LEMMA ConfAttrType ==
  \A a \in Conf, t \in Attr : a[t] \in OptStampValue
BY DEF Conf

-----------------------------------------------------------------------------
(* Nil configuration *)

(* An "empty" configuration *)
NilConf == [t \in Attr |-> None]

LEMMA NilConfMin ==
  \A a \in Conf : NilConf \preceq a
BY Zenon DEF NilConf, \preceq, OptStampValueLte

-----------------------------------------------------------------------------
(* Configuration merge *)

(* Merge two configurations.
   For each attribute, the newest is kept (see corresponding proof).
   (Conf, (.), NilConf) forms a monoid. *)
a (.) b ==
  [t \in Attr |-> IF OptStampValueLte(a[t], b[t])
                THEN b[t]
                ELSE a[t]]

LEMMA MergeClose ==
  \A a, b \in Conf : a (.) b \in Conf
BY DEF (.), Conf

LEMMA MergeAssociative ==
  \A a, b, c \in Conf : (a (.) b) (.) c = a (.) (b (.) c)
BY OptStampValueLteTransitive, OptStampValueLteAsymmetric, ConfAttrType DEF (.)

LEMMA MergeUnit ==
  \A a \in Conf : a (.) NilConf = a /\ a = NilConf (.) a
BY Zenon DEF (.), Conf, NilConf, OptStampValueLte

Monoid(A, _(\X)_, e) ==
  LET Closed      == \A a, b    \in A : a (\X) b \in A
      Associative == \A a, b, c \in A : (a (\X) b) (\X) c = a (\X) (b (\X) c)
      Unital      == \A a       \in A : a (\X) e = a /\ a = e (\X) a
  IN Closed /\ Associative /\ Unital

THEOREM MergeMonoid ==
  Monoid(Conf, (.), NilConf)
BY MergeClose, MergeAssociative, MergeUnit DEF Monoid

LEMMA MergeAfter ==
  \A a, b \in Conf : a \preceq (a (.) b) /\ b \preceq (a (.) b)
BY OptStampValueLteReflexive, OptStampValueLteAsymmetric
  DEF \preceq, (.), Conf

LEMMA MergeEqualGreater ==
  \A a, b \in Conf : a \preceq b => (a (.) b) \preceq b /\ b \preceq (a (.) b)
BY OptStampValueLteReflexive, ConfAttrType DEF \preceq, (.), Conf

LEMMA MergeBefore ==
  \A a, b, c \in Conf : a \preceq c /\ b \preceq c => (a (.) b) \preceq c
BY DEF \preceq, (.)

-----------------------------------------------------------------------------
(* Full configuration at a given date *)

(* "full" means all attributes have a value, i.e. no attribute is missing. *)
FullConfAt(d) ==
  [t \in Attr |-> MkStampValue(DefaultValue, d)]

LEMMA DefaultConfAtProperties ==
  \A d \in Date :
    LET a == FullConfAt(d)
    IN /\ a \in Conf
       /\ \A t \in Attr :
            /\ a[t] /= None
            /\ a[t] \in StampValue
            /\ DateOf(a[t]) = d
BY Assumptions DEF FullConfAt, Conf, OptStampValue

LEMMA DefaultConfAtDateLte ==
  \A d1, d2 \in Date :
    dateLte(d1, d2) => FullConfAt(d1) \preceq FullConfAt(d2)
<1> SUFFICES ASSUME NEW d1 \in Date, NEW d2 \in Date, dateLte(d1, d2), NEW t \in Attr
             PROVE  dateLte(DateOf(FullConfAt(d1)[t]), DateOf(FullConfAt(d2)[t]))
    BY DefaultConfAtProperties, Zenon DEF \preceq, OptStampValueLte
<1> QED
  BY DefaultConfAtProperties

LEMMA DefaultConfBeforeDefaultConfAt ==
  \A d \in Date : DefaultConf \preceq FullConfAt(d)
  <1> SUFFICES ASSUME NEW d \in Date, NEW t \in Attr
               PROVE  OptStampValueLte(DefaultConf[t], FullConfAt(d)[t])
    BY DEF \preceq
  <1>1. CASE DefaultConf[t] = None
    BY <1>1, Assumptions, DefaultConfAtProperties, Zenon DEF OptStampValueLte
  <1>2. CASE DefaultConf[t] /= None
    <2> USE <1>2
    <2> SUFFICES dateLte(DateOf(DefaultConf[t]), DateOf(FullConfAt(d)[t]))
      BY DefaultConfAtProperties, Zenon DEF OptStampValueLte, Conf
    <2>1. /\ DateOf(DefaultConf[t]) = MinDate
          /\ DateOf(FullConfAt(d)[t]) = d
          /\ dateLte(MinDate, d)
      BY DefaultConfAtProperties, Assumptions DEF Conf, OptStampValue
    <2>3. QED
      BY <2>1, Zenon
  <1>3. QED
    BY <1>1, <1>2

-----------------------------------------------------------------------------
(* Partial configuration predicate *)

(* A partial configuration may have missing attributes.
 * A full configuration (i.e. with no missing element) is a partial
 * configuration.
 *)
IsPartialConfAt(a, d) ==
  \A t \in Attr : a[t] /= None => DateOf(a[t]) = d

LEMMA PartialConfBeforeFullConf ==
  \A a \in Conf, d \in Date : IsPartialConfAt(a, d) => a \preceq FullConfAt(d)
  <1> SUFFICES ASSUME NEW a \in Conf, NEW d \in Date,
                      IsPartialConfAt(a, d), NEW t \in Attr
               PROVE  OptStampValueLte(a[t], FullConfAt(d)[t])
    BY DEF \preceq
  <1>1. CASE a[t] = None
    BY <1>1, Zenon DEF OptStampValueLte
  <1>2. CASE a[t] /= None
    <2> USE <1>2, DefaultConfAtProperties, Assumptions
    <2> SUFFICES dateLte(DateOf(a[t]), DateOf(FullConfAt(d)[t]))
      BY Zenon DEF OptStampValueLte, IsPartialConfAt
    <2> SUFFICES DateOf(a[t]) = d /\ d = DateOf(FullConfAt(d)[t])
      OBVIOUS
    <2> QED
      BY DEF IsPartialConfAt, FullConfAt
  <1>3. QED
    BY <1>1, <1>2

-----------------------------------------------------------------------------
(* Specification invariants *)

TypeOK ==
  /\ conf      \in Conf
  /\ reported  \in Conf
  /\ desired   \in Conf
  /\ now       \in Date
  /\ running   \in BOOLEAN
  /\ connected \in BOOLEAN

ConnectedImplyRunning ==
  connected => running

UpToDateConf ==
  connected => desired \preceq conf

ReportedLteConf ==
  reported \preceq conf

NowIncreasing ==
  dateLte(now, now')

ConfsNotInFuture ==
  \A a \in {conf, desired, reported} :
    a \preceq FullConfAt(now)

-----------------------------------------------------------------------------
(* Specification: init & events *)

Init ==
  /\ conf      = NilConf
  /\ reported  = NilConf
  /\ desired   = NilConf
  /\ now       = InitialNow
  /\ running   = FALSE
  /\ connected = FALSE

(* Device boots.
 * The conf is merged with the default conf. Since default conf is always the
 * oldest (attributes are stamped with the minimum date), it acts as a fallback.
 *)
Boot ==
  /\ ~ running
  /\ conf'    = DefaultConf (.) conf
  /\ running' = TRUE
  /\ now'     = NextDate(now)
  /\ UNCHANGED <<reported, desired, connected>>

(* The device shuts down.
 * No action with respect to the settings.
 *)
Shutdown ==
  /\ running
  /\ running'   = FALSE
  /\ connected' = FALSE
  /\ now'       = NextDate(now)
  /\ UNCHANGED <<conf, reported, desired>>

(* Device gains network connection. The conf is merged with the desired conf,
 * applying any newer setting. The conf is not reported, see the `Report` event.
 *)
Connect ==
  /\ running
  /\ ~ connected
  /\ conf'      = conf (.) desired
  /\ connected' = TRUE
  /\ now'       = NextDate(now)
  /\ UNCHANGED <<reported, desired, running>>

(* Device loses network connection.
 * No action with respect to settings.
 *)
Disconnect ==
  /\ running
  /\ connected
  /\ connected' = FALSE
  /\ now'       = NextDate(now)
  /\ UNCHANGED <<conf, reported, desired, running>>

(* Some settings are changed locally to the device, i.e. a conf whose values are
 * timestamped at "now" is merged with the local conf.
 *)
LocalChange ==
  \E c \in Conf :
    /\ IsPartialConfAt(c, now)
    /\ running
    /\ conf' = conf (.) c
    /\ now'  = NextDate(now)
    /\ UNCHANGED <<reported, desired, running, connected>>

(* Some settings are changed remotely to the device, in the desired conf. If the
 * device is connected, the changes are applied immediately. Otherwise, they will
 * on next connection (see the `Connect` event). As for local changes, the
 * remote changes are represented as a conf at "now".
 *)
RemoteChange ==
  \E c \in Conf :
    /\ IsPartialConfAt(c, now)
    /\ desired' = desired (.) c
    /\ conf'    = IF connected THEN conf (.) desired' ELSE conf
    /\ now'     = NextDate(now)
    /\ UNCHANGED <<reported, running, connected>>

(* Device reports its local conf, i.e. the local conf is merged with the
 * reported conf.
 *)
Report ==
  /\ running
  /\ connected
  /\ reported' = reported (.) conf
  /\ now'      = NextDate(now)
  /\ UNCHANGED <<conf, desired, running, connected>>

Next ==
  \/ Boot
  \/ Shutdown
  \/ Connect
  \/ Disconnect
  \/ LocalChange
  \/ RemoteChange
  \/ Report

Spec ==
  /\ Init
  /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Specification invariant proofs *)

LEMMA InitTypeOK ==
  Init => TypeOK
BY Assumptions, Isa DEF Init, NilConf, Conf, OptStampValue, TypeOK

LEMMA NextTypeOK ==
  TypeOK /\ [Next]_vars => TypeOK'
<1> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
  OBVIOUS
<1> USE Assumptions DEF TypeOK
<1>1. CASE Boot
  BY <1>1, MergeClose DEF Boot
<1>2. CASE Shutdown
  BY <1>2, Zenon DEF Shutdown
<1>3. CASE Connect
  BY <1>3, MergeClose DEF Connect
<1>4. CASE Disconnect
  BY <1>4, Zenon DEF Disconnect
<1>5. CASE LocalChange
  BY <1>5, MergeClose DEF LocalChange
<1>6. CASE RemoteChange
  BY <1>6, MergeClose DEF RemoteChange
<1>7. CASE Report
  BY <1>7, MergeClose DEF Report
<1>8. CASE UNCHANGED vars
  BY <1>8 DEF vars
<1>9. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF Next

THEOREM InvariantTypeOK ==
  Spec => []TypeOK
BY InitTypeOK, NextTypeOK, PTL DEF Spec

LEMMA NextNowIncreasing ==
  TypeOK /\ [Next]_vars => NowIncreasing
BY Assumptions DEF TypeOK, NowIncreasing, Next, vars,
 Boot, Shutdown, Connect, Disconnect, LocalChange,
 RemoteChange, Report

LEMMA InvariantNowIncreasing ==
  Spec => [][NowIncreasing]_vars
<1>1. TypeOK /\ [Next]_vars => NowIncreasing
  BY Assumptions DEF TypeOK, NowIncreasing, Next, vars,
   Boot, Shutdown, Connect, Disconnect, LocalChange,
   RemoteChange, Report
<1>2. QED
  BY <1>1, InvariantTypeOK, PTL DEF Spec

LEMMA NextDefaultConfAtNowIncreasing ==
  TypeOK /\ [Next]_vars => FullConfAt(now) \preceq FullConfAt(now')
BY NextNowIncreasing, DefaultConfAtDateLte, NextTypeOK DEF TypeOK, NowIncreasing

LEMMA DefaultConfAtNowIncreasing ==
  Spec => [][FullConfAt(now) \preceq FullConfAt(now')]_vars
BY NextDefaultConfAtNowIncreasing, InvariantTypeOK, PTL DEF Spec


(* Correct invariant *)

Correct ==
  /\ ConnectedImplyRunning
  /\ UpToDateConf
  /\ ReportedLteConf
  /\ ConfsNotInFuture

THEOREM InvariantCorrect ==
  Spec => []Correct
<1>1. Init => Correct
  <2> SUFFICES ASSUME Init PROVE Correct
    OBVIOUS
  <2> USE DEF Init
  <2>1. ConnectedImplyRunning
    BY DEF ConnectedImplyRunning
  <2>2. UpToDateConf
    BY DEF UpToDateConf
  <2>3. ReportedLteConf
    BY InitTypeOK, ConfLteReflexive DEF TypeOK, ReportedLteConf
  <2>4. ConfsNotInFuture
    BY NilConfMin, InitTypeOK, DefaultConfAtProperties DEF ConfsNotInFuture, TypeOK
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Correct
<1>2. TypeOK /\ Correct /\ [Next]_vars => Correct'
  <2> SUFFICES ASSUME TypeOK, Correct, [Next]_vars PROVE Correct'
    OBVIOUS
  <2>1. CASE Boot
    <3> USE <2>1 DEF Boot
    <3>1. ConnectedImplyRunning'
      BY DEF ConnectedImplyRunning
    <3>2. UpToDateConf'
      BY DEF Correct, ConnectedImplyRunning, UpToDateConf
    <3>3. ReportedLteConf'
      BY NextTypeOK, Assumptions, MergeAfter, ConfLteTransitive
        DEF TypeOK, Correct, ReportedLteConf, Conf
    <3>4. ConfsNotInFuture'
      BY Assumptions, DefaultConfAtProperties, NextTypeOK, DefaultConfBeforeDefaultConfAt,
        MergeBefore, NextDefaultConfAtNowIncreasing, ConfLteTransitive
        DEF Correct, ConfsNotInFuture, TypeOK
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Correct
  <2>2. CASE Shutdown
      BY <2>2, NextDefaultConfAtNowIncreasing, ConfLteTransitive, NextTypeOK, DefaultConfAtProperties \*, Assumptions
        DEF Shutdown, Correct, ConnectedImplyRunning, UpToDateConf,
            ReportedLteConf, ConfsNotInFuture, TypeOK
  <2>3. CASE Connect
    <3> USE <2>3, NextTypeOK DEF Connect, TypeOK
    <3>1. ConnectedImplyRunning'
      BY DEF ConnectedImplyRunning
    <3>2. UpToDateConf'
      BY MergeAfter DEF UpToDateConf
    <3>3. ReportedLteConf'
      BY MergeAfter, ConfLteTransitive DEF Correct, ReportedLteConf
    <3>4. ConfsNotInFuture'
      BY Assumptions, DefaultConfAtProperties, MergeBefore,
        NextDefaultConfAtNowIncreasing, ConfLteTransitive
        DEF Correct, ConfsNotInFuture
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Correct
  <2>4. CASE Disconnect
    BY <2>4, NextDefaultConfAtNowIncreasing, ConfLteTransitive, NextTypeOK, DefaultConfAtProperties
      DEF Disconnect, Correct, ConnectedImplyRunning, UpToDateConf,
          ReportedLteConf, ConfsNotInFuture, TypeOK
  <2>5. CASE LocalChange
    <3> USE <2>5, NextTypeOK DEF LocalChange, Correct, TypeOK
    <3>1. ConnectedImplyRunning'
      BY DEF ConnectedImplyRunning
    <3>2. UpToDateConf'
      BY MergeAfter, ConfLteTransitive DEF UpToDateConf
    <3>3. ReportedLteConf'
      BY MergeAfter, ConfLteTransitive DEF ReportedLteConf
    <3>4. ConfsNotInFuture'
      BY Assumptions, DefaultConfAtProperties, MergeBefore,
        PartialConfBeforeFullConf, NextDefaultConfAtNowIncreasing, ConfLteTransitive
        DEF ConfsNotInFuture
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Correct
  <2>6. CASE RemoteChange
    <3> USE <2>6, NextTypeOK DEF RemoteChange, Correct, TypeOK
    <3>1. ConnectedImplyRunning'
      BY DEF ConnectedImplyRunning
    <3>2. UpToDateConf'
      BY MergeAfter DEF UpToDateConf
    <3>3. ReportedLteConf'
      BY MergeAfter, ConfLteTransitive DEF ReportedLteConf
    <3>4. ConfsNotInFuture'
      BY MergeBefore, PartialConfBeforeFullConf, DefaultConfAtProperties,
        NextDefaultConfAtNowIncreasing, ConfLteTransitive
        DEF ConfsNotInFuture
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Correct
  <2>7. CASE Report
    <3> USE <2>7, NextTypeOK DEF Report, Correct, TypeOK
    <3>1. ConnectedImplyRunning'
      BY DEF ConnectedImplyRunning
    <3>2. UpToDateConf'
      BY MergeAfter, ConfLteTransitive DEF UpToDateConf
    <3>3. ReportedLteConf'
      BY MergeEqualGreater DEF ReportedLteConf
    <3>4. ConfsNotInFuture'
      BY MergeBefore, PartialConfBeforeFullConf, NextDefaultConfAtNowIncreasing,
        ConfLteTransitive, DefaultConfAtProperties DEF ConfsNotInFuture
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Correct
  <2>8. CASE UNCHANGED vars
    BY <2>8 DEF vars, Correct, ConnectedImplyRunning, UpToDateConf,
      ReportedLteConf, ConfsNotInFuture
  <2>9. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, InvariantTypeOK DEF Next
<1>3. QED
  BY <1>1, <1>2, InvariantTypeOK, PTL DEF Spec

=============================================================================
