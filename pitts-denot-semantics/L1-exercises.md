$$
\newcommand{\true}{\text{true}}
\newcommand{\false}{\text{false}}
\newcommand{\undefined}{\text{undefined}}
\newcommand{\skip}{\text{skip}}
\newcommand{\if}{\text{if}}
\newcommand{\state}{\text{state}}
\newcommand{\dom}{\text{Domain}}
\newcommand{\parto}{\rightharpoonup}
\newcommand{\brak}[1]{[\![#1]\!]}
$$
## exercise 1.1 -> implement `imp-` in ~~sml~~ haskell.

(See my imp repository [here](https://github.com/JakeTrevor/imp))

------
## exercise 1.2
consider the function:

$$
\begin{align*}
f_{b,c} = \lambda w \in (\Sigma \rightharpoonup \Sigma).\lambda s \in \Sigma. \\
&\if(b(s), w(c(s)), s)
\end{align*}
$$
### i. 
Show by induction on $n$ that:

$$
f_{b,c}^n (\bot)=\lambda s \in \Sigma.
\begin{cases}
c^k(s) & \exists0 \leq k < n . b(c^k(s)) = \false\\
& \wedge  \forall 0 \leq i < k. b(c^i(s)) = \true & (1)\\
\undefined & \forall 0 \leq i < n . b(c^i(s))=\true &(2)
\end{cases}
$$

In the base case, $n = 0$;
$$
\begin{align*}
f_{b,c}^0(\bot)   &= \bot\\
\bot &=\lambda \sigma \in \Sigma. \undefined
\end{align*}
$$
case $(1)$ cannot hold as no $k$ can exists such that $0 \leq k < 0$. 
In case $(2)$, $i$ can take on no values, and thus is vacuously true.
Thus it holds for the base case. 

In the inductive case, 
We assume that it holds for $n$:

$$
\begin{align*}
f_{b,c}^n (\bot) = \lambda s.
\begin{cases}
c^k(s) & \exists k \in [0,n).\\& \forall i \in [0, k).\\& b(c^i(s)) \wedge \neg b(c^k(s)) &(1)\\\\
\undefined & \forall i \in [0,n).b(c^i(s)) & (2)
\end{cases}
\end{align*}
$$

Thus we need to show that it holds for
$$
f_{b,c}(f_{bc}^n(\bot))
$$
Consider the case of some $s$ such that $(1)$ applies in $f^n$. Then some $k$ exists such that for all $i$ less than $k$, $b(c^i(s))$ is true, and $b(c^k(s))$ is false. Thus it trivially also holds for $n+1$, since $n+1 > n$. 

Next we shall consider some $s$ such that the second case applies in $f^n$, i.e. for all $i$ less than $n$, $b(c^i(s))$ is true. 

This splits further into two cases. 
First, consider that $b(c^{n}(s))$ is true. In this case, we get:
$\if(b(c^n(s)), w(c^n(s)),  c^{n-1}(s)) = \if (\true, w(c^n(s)),  c^{n-1}(s)) = w(c^n(s))$.

Thus, note that $w(c^n(s))$ is undefined, and thus case $(2)$ applies. 

Alternatively, $b(c^{n}(s))$ is false. 
In this case, we get:

$\if(b(c^n(s)), w(c^n(s)), c^{n-1}(s)) = \if (\false, w(c^n(s)),  c^{n-1}(s)) = c^{n-1}(s)$.

We assumed by the induction hypothesis that $\forall i \in [0,n). b(c^i(s))$ was true. And we have thus shown some $k =n$ such that $\exists k \in [0, n+1). \forall i \in [0,k). b(c^i(s)) \wedge \neg b(c^k(s))$, and furthermore that the value of the function when some condition holds is $c^k = c^n$. 
Thus this clearly falls into case $(1)$.
$\square$

--------

### ii.
let:
$$
w_{b,c} : \state \parto \state
$$
be the partial function defined as:
$$
w_{b,c} = \lambda s \in \state \begin{cases}
c^k(s) & \exists k \geq 0. \\& \forall i \in [0, k). \\& b(c^i(s)) \wedge \neg b(c^k(s)) &(1)\\\\
\undefined & \forall i \geq 0. b(c^i(s))  & (2)
\end{cases}
$$
Show that $w_{b,c}$ satisfies the fixed point equation:
$$
w_{b,c} = f_{b,c}(w_{b,c})
$$

Recalling that:
$$
\begin{align*}
f_{b,c} = \lambda w \in (\Sigma \rightharpoonup \Sigma).\lambda s \in \Sigma. \\
&\if(b(s), w(c(s)), s)
\end{align*}
$$

First, consider the case of some state $s$ which falls into case $(2)$ from the definition above - that is, $\forall i \geq 0. b(c^i(s))= \true$. In this case, we know that $b(s) = \true$, and thus we can write:
$$
f_{b,c}(w_{b,c})(s) = \if(\true,w(c(s), s)) = w(c(s))
$$
This corresponds to doing one iteration of the loop outside the function. Correspondingly, it suffices to show that $\forall i \geq 1. b(c^i(s))=\true$. We know however that for all $i\geq 0$, $b(c^i(s))=\true$. 
Thus the result is equivalent.


Next consider some state $s$ such that $w_{b,c}(s)$ falls into case $(1)$. We can proceed here by cases on $k$.

First, it is possible that $k$ = 0 - that is, that $b(s) = \false$. In this case, then we have:
$$f_{b,c}(w_{b,c})(s) = \if(\false,w(c(s), s)) =s$$
And we have from our definition of $w_{b,c}$ above that:
$$w_{b,c}(s) = c^k (s) = c^0 (s) = s$$
And thus the two are equal.


Alternatively, we consider the case where $k \geq 1$. In this case, we know that $b(c^i(s))=\true$ - since this holds for all $i < k$.
In this case, we can again write:
$$f_{b,c}(w_{b,c})(s) = \if(\true,w(c(s), s)) = w(c(s))
$$
by the same argument as before, we now require to show that 
$$
\exists k\geq 1. \forall i \in [0, k).  b(c^i(s)) \wedge \neg b(c^k(s))
$$
This follows trivially from the assumptions we made in considering this case - that $k \geq 1$. 
thus $w_{b,c}=f_{b,c}(w_{b,c})$
$\square$


----
### iii. describe the function $f_{b,c}$ for $b = \brak\true$ and $c = \brak\skip$
Which partial functions are fixed points of this?
what is the least fixed point?


Recall the formula for $f_{b,c}$:
$$
f_{b,c} = \lambda w. \lambda s.\if(b(s), w(c(s)), s )
$$
 By substituting the values $b$ and $c$ into the formula for $f$, we get:
 
$$
f_{\brak\true, \brak\skip}= \lambda w.\lambda s. \if (\true, w(s), s)\\
= \lambda w. \lambda s. w(s) =_{\eta} \lambda w.w
$$
In other words, any function is a fixed point of this $f$. 

The least fixed point of this $f$, according to the definition we worked out earlier, is $\bot$, the undefined function.


## 1.3

### i. Show that the following relation is a partial order:

$$
\begin{align*}
D = (\state \rightharpoonup \state)\\
w \sqsubseteq w' \implies \forall s\in \dom(w). s \in \dom(w') \wedge w(s) = w'(s)
\end{align*}
$$
A partial order is:
1. reflexive
2. transitive
3. anti-symmetric

#### 1. reflexive
$w \sqsubseteq w'$
First, note that every element in the  domain of $w$ is clearly in the domain of $w$. Furthermore, $w(s) = w(s)$. Thus the relation is reflexive.

#### 2. transitive
$$
w \sqsubseteq w' \wedge w' \sqsubseteq w'' \implies w \sqsubseteq w''
$$
First, note that if every element in the domain of $w$ is in the domain is in the domain of $w'$, and every element in the domain of $w'$ is in the domain of $w''$, then it must also be the case that every element in the domain of $w$ is also in the domain of $w''$.

Furthermore, if $w(s) = w'(s)$, and $w'(s) = w''(s)$, then due to the transitive nature of equality, then $w(s) = w''(s)$.
Thus the relation is transitive.

3. anti-symmetric. 

$$
w \sqsubseteq w' \wedge w' \sqsubseteq w \implies w = w'
$$

first, note that if all elements of the domain of $w$ are in the domain of $w'$, and all elements of the domain of $w'$ are in the domain of $w$, then the domains must be equal; essentially:
$$
\begin{align*}
\dom(w) \subseteq \dom(w') \wedge \dom(w') \subseteq \dom(w) \\\implies \dom (w) = \dom(w')
\end{align*}
$$
Having established that the domains are equivalent, it suffices to show that all elements in the domain are mapped to the same values under $w$ and $w'$. This however is also given by the definition of $w \sqsubseteq w'$. Thus the relation is anti-symmetric.

Thus we have shown that the relation is a partial order. $\square$

### ii. show that $\bot$ is the least element of this partial order

The least element is one such that $\forall d \in D. \bot \sqsubseteq d$
recall that:
$$
\begin{align*}
D = (\state \rightharpoonup \state)\\
w \sqsubseteq w' \implies \forall s\in \dom(w). s \in \dom(w') \wedge w(s) = w'(s)\\
= \dom(w) \subseteq \dom(w') \wedge  \forall s \in \dom(w). w(s) = w'(s)
\end{align*}
$$
and that $\bot$ is given by:
$$
\bot = \sigma \in \Sigma. \undefined
$$
Thus the domain of $\bot$ is $\emptyset$. Thus it is vacuously true that $\forall w \in D. \dom(\bot) \subseteq \dom(w)$, as $\emptyset$ is a subset of any other set.

Furthermore, since there are no elements in $\emptyset$ the domain of $\bot$, it is similarly true that all elements of $\dom(\bot)$ are mapped to the same value under any other $w \in D$.
Thus all $\forall w \in D. \bot \sqsubseteq w$. 
$\square$


## 1.4: 
$w = f(w) \implies w_\infty \sqsubseteq w$
i.e. prove that $w_\infty$ is the least fixed point of $f$. 

Furthermore, 
$$
\forall w \in (\state\to\state). w= f_{b,c}(w) \implies w_{b,c} \sqsubseteq w
$$
