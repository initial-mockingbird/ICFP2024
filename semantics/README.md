# Extended Semantics

## BNF Grammar

We try to stick with a very standard grammar for a lambda calculus with variable assignment. With a couple of minor differences:

- Every argument in a lambda expression is explicitly typed.
- We denote the set of basic types as $B$.
- We add Type Variables, Abstractions and Applications. Although not currently employed, it allows us to write the one existential triplet the language uses to model the `Lazy*` type.
- We add an existential triplet to model `Lazy*`. It contains the type witness, the value, and a function to forcefully evaluate the value.
- We have 3 environments: Gamma (names to types), E (names to memory locations) and S (memory locations to expressions). As a shorthand, we write $\varphi_{i,j,k}$ for $E_i,S_j,\Gamma_k$.
- Every expression can result in a closure $<e,\varphi>$

## Typing Rules


- EL: Provides a syntactic sugar to evaluating the 3 environments. We read $\varphi_{i,j,k} \vdash x : \tau [e]$, as:  the variable $x$ holds the expression $e$ of type $\tau$ in the context $\varphi_{i,j,k}$
- E-Abs: Classical lamba abstraction
- T-App: Classical type level lamba application.
- Defer: acts as a constructor for the $Lazy$ type, which models unreduced expressions.
- Formula: Formula only works on variables. Gets the contents of the variable WITHOUT applying any big steps to it.
- BT: The function $bt$ is used only on the formal semantics as a helper. It's a type-level function which returns the basic type of the argument.
- STR/STT/STA: Defines a **S**ub**T**ype relation which is **R**eflexive, **T**transitive, and **A**ntisimetric.
- F-ST: States the subtyping relation for functions as per usual: contra-variant over the argument and co-variant over the return.
- VL-ST: Any Basic type $\tau$ is subtype of  $Lazy<\tau>$. That is, any reduced expression can also be thought as a non-necessarily reduced expression.
- LL-ST: Every Lazy expresion, is subtype of an even more lazy expression. That is, if a lazy expression $l$, can be reduced to a basic type in $n$ big steps, it can also be reduced to the same basic type in $n+1$ big steps.
- LL*-ST: Any type is a subtype of the $Lazy*$. We'll discuss what $Lazy*$ stands for in the next section.
- E-App: Classic function application.
- $\bot$: Zilly provides a bottom value which inhabits evert type for errors.
- Closure: All closures have the same type as the value they wrap.
- F-RT: Functions expressions are reduced to function expressions.
- I-RT: Integer values are reduced to integer values
- LN-RT: A value of type $Lazy<Lazy<\tau>>$ which can be reduced to a basic value in $n+1$ big steps, is reduced to a value of type $Lazy<\tau>$ which can be reduced to a basic type in $n$ big steps.
- L-RT: A value of type $Lazy<B>$ can be reduced to a basic type $B$ in exactly one big step.
- L*-RT: A value of type $Lazy*<\tau>$, which can originally be reduced to a basic type in zero or more steps, is reduced to a value of the same type.
- FE: $feval$ forcefully evaluates any expression to its basic type.

## Operational semantics of expressions

- BT-B:  The basic type of a basic type is itself.
- BT-LB: The basic type of $Lazy<B>$, is $B$.
- BT-LL: If we know that the basic type of $\tau_1$ is $\tau_2$, then it must also be the basic type for $Lazy<\tau_1>$.
- E-Int: Number literals are reduced to themselves.
- E-Fun: Function literals are reduced to a closure that contains themselves.
- E-FClosure: Function closures are reduced to themselves.
- feval-1: force evaluating an expression of a basic type, is the same as applying one big step to it.
- feval-2: force evaluating an unreduced expression is the same as applying one big step to it, and then force evaluating its result. Since there is no way of producing infinite-depth lazy expressions without falling into infinite recursion. $feval$ always ends on its input.
- Var-RValue: Notice that every variable is actually a reference. And notice that applying one big step to an expression can chance its result. Thus we define variable evaluation as looking up its content, and applying one big step to it.
- D-Eval: Evaluating a deferred expression yields a closure with its body. This is necessary due to possible scoping issues.
- C-Eval: Evaluating any NON-FUNCTION closure results in evaluating the wrapped expression over the wrapped contexts.
- F-eval: We defined the formula function as a lookup in the 3 environments.
- E-App: Function application is the same as in strict languages with object-reference passing: We apply one big step to both the function (to get a function closure) and the argument. And then, after allocating a new memory location, and assigning the variable argument to the formal argument, we apply one big step to the function body.
- Minus: Denotationally takes the difference of its arguments.
- Less-True, Less-Falce: Less returns 1 if the first value is less than the second one, else it returns -1.
- If-True, If-False: False clasically defined.
- Subtype-Replace: Subtyping replacement clasically defined.
 