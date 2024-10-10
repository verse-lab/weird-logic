# weird-logic

## initial idea with examples

A minimum imperative language *IMP* :

$$e ::= x~|~b \in Bool ~|~ n \in Nat~|~e \oplus e $$ 
$$\oplus ::= + | \times | < | == | \vee | \wedge$$
$$c ::= x:=e ~|~ output ~e ~| ~skip~ | ~c;c ~|~ \texttt{if} ~e ~\texttt{then} ~c ~\texttt{else} ~c ~| ~\texttt{while} ~e ~\texttt{do}~ c$$

A simplified C-like language $Toy^C$ :
$$e ::= x~|~ i ~|~ e_1 \oplus e_2 ~|~ null ~|~ *e ~|~ \&lv $$
$$ lv ::= x ~|~ *lv$$
$$ c ::= p(e_1, .., e_n) ~|~ lv :=e ~|~ output ~e ~|~ skip ~|~ c;c ~|~ \texttt{if} ~e ~\texttt{then} ~c ~\texttt{else} ~c ~| ~\texttt{while} ~e ~\texttt{do}~ c$$

### DOP attack
Take DOP as an example where *IMP* is the source language, $Toy^C$ is the target language.

```c
// in IMP language
    Program J: 
    P : {x = x0 ∧ y = y0 ∧ a >= 0 ∧ b >= 0}
    output x
    output y
    r := y;
    d := 0;
    while x<=r do {
        r := r + a // must be increasing because no negative variable in IMP (a>=0)
        x := x + b
        d := d + 1
    }
    output d;
    output r; // r > y because r is increasing
    Q : {x > r ∧ r = y0 + d * a ∧ x = x0 + d * b}

// in toyC language
    P : {x = x0 ∧ y = y0 ∧ a = -x ∧ b = 0}
    procedure main (x, y; a, b, d, r){ // integers
        output x
        output y
        r := y;
        d := 0;
        while x<=r do {
            r := r + a 
            x := x + b
            d := d + 1
        }
        output d;
        output r;
    }
    Q : {x > r ∧ y0 = d * x0 + r}
    G = main();
```
A DOP attack can be written as follows:
$$A \triangleq main(x,y; a, b, d, r) ( a:=-x; b:=0; d:=0; r:=0; hole(x, y, d, r, a, b))$$

We say $A \in WM(J)$, because $\neg \exist C^S. B(C^S[J]) \mapsto B(A[J\downarrow])$. there is no such a trace/output in the $J$ *IMP* program can be mapped to the trace/output in $J\downarrow$ in $Toy^C$ language.

#### Prove
1. Prove the attack $A$ is an exploit.

In unrealiziability logic, the problem can be encoded as follows:
$$ \{|x = x0 ∧ y = y0 ∧ r = r0 ∧ d = d0 ∧a0 >= 0 ∧ b0 >= 0 |\}~ J(a=a0;b=b0;) ~\{|\neg (x > r ∧ y0 = d * x0 + r)|\} $$

$J(a=a0;b=b0;)$ is a set of programs where $a$ and $b$ are initialized to different constant values. Then, use unrealizability logic

2. Prove the mitigation measure effective.

Define a mitigation measure $M$ for the attack $A$: check and change all negative variables to 1 at the beginning of the execution. The effect of $M$ to $J\downarrow$ can be wriiten as the following pseudocode:

```c
    P : {x = x0 ∧ y = y0 ∧ a = -x ∧ b = 0}
    procedure main (x, y; a, b, d, r){ // integers
        if a<0 then a=1
        if b<0 then b=1
        output x
        output y
        r := y;
        d := 0;
        while x<=r do {
            r := r + a 
            x := x + b
            d := d + 1
        }
        output d;
        output r;
    }
    old Q : {x > r ∧ y0 = d * x0 + r}
    G = main(); 
```

We say a mitigation measure is effective for the attack $A$ iff
$$\forall V, \exist C^S. B(C^S[V]) \mapsto B(A[V\downarrow_M])$$
or
$$\forall V, \not \exist C^T. B(C^T[V\downarrow_M]) \mapsto B(A[V\downarrow])$$

\downarrow_M is the compilation with the mitigation method. In other words, not matter how V is defined, the context $A$ is not an exploit. Here, $B(A[V\downarrow_M])$ has changed(output is different). 

Write in unrealiziability logic:
$$ \{|x = x0 ∧ y = y0 ∧ r = r0 ∧ d = d0 ∧ a=-x0 ∧ b=0 |\}~ J\downarrow_M ~\{|\neg (x > r ∧ y0 = d * x0 + r)|\} $$
Intuitively, it says the original attack is unrealizable in newly compiled program.

A type of attack, such as all DOP attacks, defined as $AT$, is a set of exploit $A$ while $A \in AT$. We say a mitigation measure is effective for a type of attack iff
$$\forall V \in P, \forall A \in AT, \exist C^S. B(C^S[V]) \mapsto B(A[V\downarrow])$$
