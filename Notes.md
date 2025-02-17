## Notes

The vulnerable program:
```C
int m, n;
int p, q, *a, *b, *c;
char bug[1024];
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
char bug[1024];
int secret;
...
{m=_*n=_*p=_*q=_*a->_*b->_*c->_}
while(m--){
    {m!=-1*n=_*p=_*q=_*a->_*b->_*c->_}
    init;
    {m=_*n=_*p=_*q=_*a->_*b->_*c->_}
    if(n==0)
        {n=0*a->_}
        printf("%d", *a);
        {n=0*a->_}
    else if(n>10)
        {n>10*p=_*b->_}
        *b = p;
        {n>10*p=_*b->p}
    else if(n>5)
        {n>5/\ \not n>10 * c->v1 * q=v2}
        *c += q;
        {n>5/\ \not n>10 * c->v1+q * q=v2}
}
{m=-1*n=_*p=_*q=_*a->_*b->_*c->_}
```
Hyper logic triples:
$$\{P\}\left[ \begin{array}{l} p \in C_- : p;C \\ l \in L_- : l\end{array} \right] 
\left\{ \begin{array}{l} C^- |~\forall~l \in L, \exist~p \in C_- \\
L^- |~C(p) = L(l) \end{array}\right\}$$

Program state: $\sigma : Var \to Val$

Let $l_1 : init (a=x); vs_3$, the triple for $l_1$: $\{a\mapsto \_ * x \mapsto v\}l_1: init (a=x);vs_3\{a \mapsto v* x \mapsto v\}$

$p_1$ is the payload: $\{(m=0, n=0, a=x )\}$, the triple for $p_1;C$: $\{m \neq 0 * a\mapsto \_ * x \mapsto v\} p_1;C \{n=0 \wedge m=-1*a\mapsto v * x \mapsto v\}$

$C(p_1)$ is one execution of $C$ equivalent to $L(l_1)$. But $m,n$ do not exist in language $L$. How to define execution equivalence in C and L?



$\sigma_{l1} \leadsto^{L(l_1)} \sigma_{l2}$

$\sigma_{p1} \leadsto^{C(p_1)} \sigma_{p2}$

$L(l_1) = C(p_1) \Leftrightarrow \sigma_{p1} \Rightarrow \sigma_{l1} \wedge \sigma_{p2} \Rightarrow \sigma_{l2}$