## Notes

The vulnerable program:
```C
int m, n;
int p, q, *a, *b, *c;
char buf[1024];
int secret;
...
while(m--){
    gets(buf);
    if(n==0)
        printf("%d", *a);
    else if(n>10)
        *b = p;
    else if(n>5)
        *c += q;
}
```
The attack grammar:
```
Value           Val         Integers
Valid Vars      Var         a, b, c, p, q
Initialisers    init    ::= Var = Val
Valid Stmt      vs1     ::= *b=p
                vs2     ::= *c=*c+q
                vs3     ::= print("%d",*a)
Attack          attack  ::= (init;(vs1+vs2+vs3) )*
```
Replace Init with the vulnerable line:
```C
int m, n;
int p, q, *a, *b, *c;
char buf[1024];
int secret;
...
{m=_/\n=_/\p=_/\q=_*a->_*b->_*c->_}
while(m--){
    {m!=-1/\n=_/\p=_/\q=_*a->_*b->_*c->_}
    init;
    {m=_/\n=_/\p=_/\q=_*a->_*b->_*c->_}
    if(n==0)
        {n=0*a->_}
        printf("%d", *a);
        {n=0*a->_}
    else if(n>10)
        {n>10/\p=_*b->_}
        *b = p;
        {n>10/\p=_*b->p}
    else if(n>5)
        {n>5/\ \not n>10 * c->v1 * q=v2}
        *c += q;
        {n>5/\ \not n>10 * c->v1+q * q=v2}
}
{m=-1/\n=_/\p=_/\q=_*a->_*b->_*c->_}
```
Hyper logic triples:
$$\{P\}\left[ \begin{array}{l} p \in C_- : p;C \\ l \in L_- : l\end{array} \right] 
\left\{ \begin{array}{l} C^- |~ \forall ~l \in L_-, \exist~p \in C_- \\
L^- |~C^-(p) = L^-(l) \end{array}\right\}$$

### Example 1
#### default grammar

Let $l_1 : init (a=x); vs_3$, the triple for $l_1$: $\{P_l: a\mapsto \_ * x \mapsto v\}l_1: init (a=x);vs_3\{Q_l: a =x* x \mapsto v\}$

$p_1$ is the payload: $\{(m=0, n=0, a=x )\}$, $p_1;C$ replaces init with payload assignments in $C$.

the triple for $p_1;C$: $\{P_c: m \neq 0 * a\mapsto \_ * x \mapsto v\} p_1;C \{Q_c: n=0 \wedge m=-1 \wedge a=x * x \mapsto v\}$

$C(p_1)$ is one execution of $C$ that is equivalent to $L(l_1)$. But $m,n$ do not exist in language $L$. How to define execution/context equivalence in C and L?



$\sigma_{l1} \leadsto^{L(l_1)} \sigma_{l2}$

$\sigma_{p1} \leadsto^{C(p_1)} \sigma_{p2}$

$L(l_1) = C(p_1) \Leftrightarrow \sigma_{p1} \Rightarrow \sigma_{l1} \wedge \sigma_{p2} \Rightarrow \sigma_{l2}$

or

$L(l_1) \sim C(p_1) : P_c \Rightarrow P_l \wedge Q_c \Rightarrow Q_l$

or 

$L(l_1) \sim C(p_1) : P_l \wedge P_c \Rightarrow Q_c \wedge Q_l$

### Example 2
#### Change symbols in grammar
Doppler generates another equivalent grammar:
```
Value           Val         Integers
Valid Vars      Var         h, k, x, y, z
Initialisers    init    ::= Var = Val
Valid Stmt      vs1     ::= *k=y    
                vs2     ::= *x=*x+z
                vs3     ::= print("%d",*h)
Attack          attack  ::= (init;(vs1+vs2+vs3) )*
```
Let $l_2 : init (k=v, y=val); vs1:*k=y$

the triple for $l_2$: $\{P_l: y=\_ * k\mapsto \_ * v \mapsto \_\}l_1: init (k=v, y=val);vs_1\{Q_l: y=val \wedge k=v * v \mapsto val \}$

Doppler generates a correct payload $p_2$: $\{(m=0, n=11, b=v, p=val )\}$

the triple for $p_2;C$:

$\{P_c: m \neq 0 \wedge p = \_ * b\mapsto \_ * v \mapsto \_\} p_1;C \{Q_c: m=-1 \wedge n=11 \wedge p=val \wedge b=v *v\mapsto val \}$

To evaluate $C(p_2) = L(l_2)$:

In preconditions, both have 3 disjointed variables in the heap. 
In postconditions, the same values are store in the heap.

$P_l \wedge P_c \Rightarrow Q_c \wedge Q_l$

### Example 3
#### Doppler generates correct grammar but wrong payload for the program in Example 1
Let $l_1 : init (a=x); vs_3$, the triple for $l_1$: $\{P_l: a\mapsto \_ * x \mapsto v\}l_1: init (a=x);vs_3\{Q_l: a = x * x \mapsto v\}$

The correct payload should be $\{(m=0, n=0, a=x )\}$, But we get a wrong payload:

$p_1'$: $\{(m=1, n=0, a=x )\}$

The program would execute print("%d", *a) twice.

the triple for $p_1';C$: $\{P_c: m \neq 0 * a\mapsto \_ * x \mapsto v\} p_1;C \{Q_c: n=0 \wedge m=-1 \wedge a=x * x \mapsto v\}$

$C(p_1') = L(l_1)$ still holds.

### Example 4
#### A nonequivalent but still correct grammar 
Another grammar $G'$:
```
Value           Val         Integers
Valid Vars      Var         a, b, c, p    // lack variable p
Initialisers    init    ::= Var = Val
Valid Stmt      vs1     ::= *b=p
                vs2     ::= *c=*c+1       // *c+p is changed to *c+1
                vs3     ::= print("%d",*a)
Attack          attack  ::= (init;(vs1+vs2+vs3) )*
```
$G' \subset G $

Let $l_4$ : $init (c=v); vs_2$, get the triple for $l_4$:
$\{P_l: v\mapsto val* c \mapsto \_\}l_1: init (c=v);vs_2\{Q_l: c=v * v \mapsto val+1 \}$

An executable payload is $p_4$: $\{(m=0,n=7,q=1)\}$.

The triple for $p_4;C$:

$\{P_c: m \neq 0 * v\mapsto val* c \mapsto \_\}p_4;C\{Q_c: m=-1 \wedge n=7 \wedge q=1 \wedge c=v * v \mapsto val+1 \}$

$C(p_4') = L(l_4)$ still holds.

## Triples

$$\bold{P} \vdash \{P\}\left[ \begin{array}{l} C \\ l \in L : l\end{array} \right] 
\left\{ \begin{array}{l} V_p |~ \forall ~l \in L, \exist~p \in P \\
V_L |~ Q(p,l,V_p(p), V_L(l)) \end{array}\right\}$$

$$Q(-,-,v_p,v_l) \triangleq [v_p = v_l]*true$$

For instance,

$$Q(p,l,v_p,v_l)= \langle a,p \rangle \mapsto x * \langle x,p \rangle \mapsto v_p * \langle a,l \rangle \mapsto x * $$
$$\langle x,l \rangle \mapsto v_l * [v_p = v_l]$$

### Example 1
Program:
```c
int main(){
    int *a, b, v;
    init; // memory corruption
    ...
    *a = v;
    b = b +1;
    return;
}
```
Grammar:
```
Val     Integers
Var     a, b, v
Init ::= Var = Val
vs1 ::= *a = v 
vs2 ::= b = b+1
Attack ::= init;vs1;vs2
```
Tripple

$$\{\langle a, \_ \rangle \mapsto \_ * \langle b, \_ * \rangle \mapsto \_ \langle v, \_ \rangle \mapsto \_ \}\left[ \begin{array}{l} p \in P : p;C \\ l \in L : l\end{array} \right] 
\left\{ \begin{array}{l} V_P |~ \forall ~l \in L, \exist~p \in P \\
V_L |~ Q(p,l,V_P(p), V_L(l)) \end{array}\right\}$$

$$Q(p,l,V_P(p), V_L(l)) := \{\langle a, p \rangle \mapsto V_P(p,a) * \langle b, p \rangle \mapsto V_P(p,b) * \langle v, p \rangle \mapsto V_P(p,v) * \\
\langle a, l \rangle \mapsto V_L(l,a) * \langle b, l \rangle \mapsto V_L(l,b) * \langle v, l \rangle \mapsto V_L(l,v) * \\
[V_P(p,a)=V_L(l,a) \wedge V_P(p,v)=V_L(l,v) \wedge V_P(p,b) = V_L(l,v)]\}$$

Abbreviation: $V_P(p,\_)$ is written as $V_p(\_)$

Step 0: Replace $L$ with $Init;vs_1;vs_2$

Step 1: Seq

$$\{\langle a, \_ \rangle \mapsto \_ * \langle b, \_ \rangle \mapsto \_ * \langle v, \_ \rangle \mapsto \_ \}\left[ \begin{array}{l} p \in P : p;C \\ l \in Init : l \end{array} \right] 
\left\{ \begin{array}{l} V_P |~ \forall ~l \in Init, \exist~p_1 \in P \\
V_{Init} |~ \langle a, p_1 \rangle \mapsto V_p(Init_a) * \langle b, p_1 \rangle \mapsto V_p(Init_b) * \langle v, p_1 \rangle \mapsto V_p(Init_v) * \\
 \langle a, l \rangle \mapsto V_l(Init_a) * \langle b, l \rangle \mapsto V_l(Init_b) * \langle v, l \rangle \mapsto V_l(Init_v) * \\
 [V_p(Init_a)=V_L(Init_a) \wedge V_p(Init_b)=V_L(Init_b) \wedge V_p(Init_v)=V_L(Init_v)]\end{array}\right\}$$

 Define $v_{init-a} = V_p(Init_a) = V_L(Init_a)$, and the same for $v_{init-b}, v_{init-v}$

$$\{\langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \}\left[ \begin{array}{l} p \in P: p;p_1;C \\ l \in [vs_1;vs_2]: l \end{array} \right] 
\left\{ \begin{array}{l} V_{P} |~  \forall l \in [vs_1;vs_2], \exist p_2 \in P\\
V_{[vs_1;vs_2]} |~ \langle a, \_ \rangle \mapsto v_{Init-v} * \langle b, \_ \rangle \mapsto v_{Init-b}+1 * \langle v, \_ \rangle \mapsto v_{Init-v}  \end{array}\right\}$$

Step 2: Frame

only one element in $[vs_1;vs_2]$, $p_2$ is None.

$$\{\langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \}\left[ \begin{array}{l} p_1;C \\ vs_1;vs_2 \end{array} \right] 
\left\{ \begin{array}{l} V_{p_1} |~  \\
V_{vs_1;vs_2} |~ \langle a, \_ \rangle \mapsto v_{Init-v} * \langle b, \_ \rangle \mapsto v_{Init-b}+1 * \langle v, \_ \rangle \mapsto v_{Init-v}  \end{array}\right\}$$

Step 3: Seq

$$\{\langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \}\left[ \begin{array}{l} p_1;C \\ vs_1\end{array} \right] 
\left\{ \begin{array}{l} V_{p_1} |~  \\
V_{vs_1} |~ \langle a, \_ \rangle \mapsto v_{Init-v} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \end{array}\right\}$$

$$\{\langle a, \_ \rangle \mapsto v_{Init-v} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \}\left[ \begin{array}{l} p_1;C \\ vs_2\end{array} \right] 
\left\{ \begin{array}{l} V_{p_1} |~ \\
V_{vs_2} |~ \langle a, \_ \rangle \mapsto v_{Init-v} * \langle b, \_ \rangle \mapsto v_{Init-b}+1 * \langle v, \_ \rangle \mapsto v_{Init-v} \end{array}\right\}$$


### Example 2
An example with $+$ in the grammar.
The program:
```c
int main(){
    int *a, b, v, c;
    init; // memory corruption
    ...
    if(c>0)
        *a = v;
    else
        b = b +1;
    return;
}
```
Grammar:
```
Val     Integers
Var     a, b, v
Init ::= Var = Val
vs1 ::= *a = v 
vs2 ::= b = b+1
Attack ::= init;(vs1+vs2)
```

Step 1: The tripple for the $Init$ part is the same as the above. The other part:
$$ P \vdash \{\langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} * p\}\left[ \begin{array}{l} C(p) \\ l \in [vs_1+vs_2] : l \end{array} \right] 
\left\{ \begin{array}{l} V_{C} |~  \forall l \in [vs_1+vs_2], \exist p_2 \in P\\
V_{[vs_1+vs_2]} |~ [\langle a, \_ \rangle \mapsto v_{Init-v} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v}] \vee \\
[\langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b}+1 * \langle v, \_ \rangle \mapsto v_{Init-v}] \end{array}\right\}$$

Step 2: Condition

$$\{\langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \}\left[ \begin{array}{l} p \in P: C(p) \\ l \in [vs_1] : l \end{array} \right] 
\left\{ \begin{array}{l} V_{p_2;p_1} |~  \forall l \in [vs_1], \exist p_3 \in P\\
V_{[vs_1]} |~ \langle a, \_ \rangle \mapsto v_{Init-v} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \end{array}\right\}$$

$$\{\langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \}\left[ \begin{array}{l} p \in P: C \\ l \in [vs_2] : l \end{array} \right] 
\left\{ \begin{array}{l} V_{p_2;p_1} |~  \forall l \in [vs_2], \exist p_3 \in P\\
V_{[vs_2]} |~ \langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b}+1 * \langle v, \_ \rangle \mapsto v_{Init-v} \end{array}\right\}$$

Step 3: Frame

$$\{\langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \}\left[ \begin{array}{l} C \\ vs_1 \end{array} \right] 
\left\{ \begin{array}{l} V_{p_2;p_1} |~  \\
V_{vs_1} |~ \langle a, \_ \rangle \mapsto v_{Init-v} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \end{array}\right\}$$

$$\{\langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b} * \langle v, \_ \rangle \mapsto v_{Init-v} \}\left[ \begin{array}{l} C \\ vs_2 \end{array} \right] 
\left\{ \begin{array}{l} V_{p_2;p_1} |~  \\
V_{vs_2} |~ \langle a, \_ \rangle \mapsto v_{Init-a} * \langle b, \_ \rangle \mapsto v_{Init-b}+1 * \langle v, \_ \rangle \mapsto v_{Init-v} \end{array}\right\}$$

1. revise if-else 
2. prefix - remove
3. C
4. write rule for seq and if, do proofs systematically
