/* Imperative Objects 
 * Replacement for Chapter 27, 32
 */

/* Treat Object as syntactic
 * sugar -- a way to create types --- for now.
 * Ignore the "::*=>*" stuff here also.  
 */
Object Methods::*=>* = {Some R, { state : R, methods : Methods R }};

/* Sugar again, for now */
CounterM R = {inc : R -> Unit, get : R -> Nat};

/* Using the sugar */
Counter = Object CounterM;

CounterRep = {c : Ref Nat};

counterMethods = 
  {inc = lambda rep : CounterRep . rep.c := succ (!(rep.c)),
   get = lambda rep : CounterRep . !(rep.c) };

sendinc = lambda c : Counter . 
  let {R, obj} = c in
    obj.methods.inc(obj.state);
sendget = lambda c : Counter .
  let {R, obj} = c in
    obj.methods.get(obj.state);

makeCounter =
  lambda n : Nat .
    {*CounterRep, { state = {c = ref n}, methods = counterMethods } }
    as Counter;

let c = makeCounter 3 in
  (sendinc c; sendinc c; sendget c);
  
SetCounterM R = {inc : R -> Unit, get : R -> Nat, set : R -> Nat -> Unit};

SetCounter = Object SetCounterM;

SetCounterRep = CounterRep;

setCounterMethodsH = 
  lambda R <: SetCounterRep . 
    lambda self : Source (SetCounterM R) .
      let super = counterMethods in
        {inc = lambda rep : R . 
                 (!self).set rep (succ((!self).get rep)),
         get = super.get,
         set = lambda rep : R . lambda n : Nat . rep.c := n } 
      as SetCounterM R;

univFunc = lambda x:Top . error;

dummySetCounterMethods = 
  { inc = univFunc, get = univFunc, set = univFunc }
  as SetCounterM SetCounterRep;

setCounterMethods =
  let vtable = ref dummySetCounterMethods in
    (vtable := setCounterMethodsH[SetCounterRep] vtable; !vtable);

makeSetCounter = lambda n : Nat .
  {* SetCounterRep, { state = {c = ref n}, methods = setCounterMethods } } 
  as SetCounter;

let c = makeSetCounter 8 in
  (sendinc c; sendinc c; sendget c);
  

InstrSetCounterM R = { inc : R -> Unit, 
                       get : R -> Nat, 
                       set : R -> Nat -> Unit,
                       acc : R -> Nat };

InstrSetCounterRep = { c : Ref Nat, a : Ref Nat };

InstrSetCounter = Object InstrSetCounterM;

sendacc = lambda c : InstrSetCounter .
  let {R, obj} = c in
    obj.methods.acc(obj.state);

instrSetCounterMethodsH =
  lambda R <: InstrSetCounterRep .
    lambda self : Source (InstrSetCounterM R) .
      let super = setCounterMethodsH[R] self in
        {inc = super.inc,
         get = super.get,
         set = lambda rep : R . 
                 lambda n : Nat . 
                   (super.set rep n ; rep.a := (succ( !(rep.a)))),
         acc = lambda rep : R . !rep.a }
      as InstrSetCounterM R;

dummyInstrSetCounterMethods = 
  { inc = univFunc, get = univFunc, set = univFunc, acc = univFunc }
  as InstrSetCounterM InstrSetCounterRep;

instrSetCounterMethods =
  let vtable = ref dummyInstrSetCounterMethods in
    (vtable := instrSetCounterMethodsH[InstrSetCounterRep] vtable; !vtable);

makeInstrSetCounter =
  lambda n : Nat .
    {*InstrSetCounterRep, { state = { c = ref n, a = ref 0 },
                            methods = instrSetCounterMethods }}
    as InstrSetCounter;

ic = makeInstrSetCounter 13;

(sendinc ic; sendinc ic; sendget ic);

(sendacc ic);


/* From here on, we need Chapter 30 */


CloneM R = { clone : R -> R };

Clone = Object CloneM;

sendclone =
  lambda M <: CloneM .
    lambda c : Object M .
      let {R, obj} = c in
        {* R, { state = obj.methods.clone(obj.state),
                methods = obj.methods }} as Object M;

CloneSetCounterM R = { inc : R -> Unit, 
                       get : R -> Nat, 
                       set : R -> Nat -> Unit, 
                       clone : R -> R };

CloneSetCounter = Object CloneSetCounterM;

func = lambda cc : CloneSetCounter .
         (sendclone[CloneSetCounterM] cc) as CloneSetCounter;
  
CloneSetCounterRep = SetCounterRep;

cloneSetCounterMethodsH =
  lambda R <: CloneSetCounterRep .
    lambda self : Source (SetCounterM R) .
      lambda cloneImpl : R -> R .
        let super = setCounterMethodsH[R] self in
          { inc = super.inc,
            get = super.get,
            set = super.set,
            clone = cloneImpl}
          as CloneSetCounterM R;

dummyCloneSetCounterMethods =
    { inc = univFunc, get = univFunc, set = univFunc, clone = univFunc}
    as CloneSetCounterM CloneSetCounterRep;

makeCloneSetCounterRep = lambda n:Nat .
    { c = ref n } 
    as CloneSetCounterRep;

cloneSetCounterMethods =
  let vtable = ref dummyCloneSetCounterMethods in
    (vtable := cloneSetCounterMethodsH[CloneSetCounterRep] vtable
      (lambda rep : CloneSetCounterRep . makeCloneSetCounterRep (!(rep.c)));
      !vtable);

makeCloneSetCounter = lambda n : Nat .
  {*CloneSetCounterRep, {state = makeCloneSetCounterRep n, 
                        methods = cloneSetCounterMethods}}
  as CloneSetCounter;

c1 = makeCloneSetCounter 2;

c2 = (sendinc c1; sendinc c1; sendclone[CloneSetCounterM] c1);

(sendinc c1; sendinc c1; sendget c1);

(sendinc c2; sendget c2);
