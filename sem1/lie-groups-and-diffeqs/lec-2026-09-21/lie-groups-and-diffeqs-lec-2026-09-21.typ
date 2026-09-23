#import "template-lec.typ": *
#show: doc => conf([Группы Ли и ДУ. Лекция (21.09.2026)], doc)

*Задача*
$
  V = (v^i), thick W = (w^i)\
  [V, W] = ?
$

_Решение_

$
  V(x^i) = sum_(i=1)^n v^j (partial x^i) / (partial x^j) = sum_i
  v^j delta_j^i = v^i
$

$
  [V, W](x^i) = V(W(x^i)) - W(V(x^i)) = V(w^i) - W(v^i)
$



#theorem([], [
  $forall V, W, Z$ - в.п.

  $
    [V[W, Z]] + [Z[V,W]] + [W[Z,V]] = 0
  $

  _Доказательство_
  $
    [V[W, Z]](f) + [Z[V,W]](f) + [W[Z,V]](f) =\
    V([W,Z](f)) - [W,Z](V(f)) + dots =\
    V(W(Z(f))) - V(Z(W(f))) - W(Z(V(f)) + Z(W(V(f))) +\
    Z(V(W(f))) - Z(W(V(f))) - V(W(Z(f)) + W(V(Z(f))) +\
    W(Z(V(f))) - W(V(Z(f))) - Z(V(W(f)) + V(Z(W(f))) = 0
  $
])

#theorem[][
  $f: M -> N$ - диф-м, $forall V, W$ - в.п. на $M$
  $
    f_* ([V,W]) = [f_* V, f_* W]
  $

  _Доказательство_
  $
    f: {y^alpha = f^alpha (x^i)}, quad V = (v^i), thick
    W = (w^i)
  $

  $
    (f_* V)^alpha = (partial f^alpha) / (partial x^i) v^i\
    (f_* W)^alpha = (partial f^alpha) / (partial x^i) w^i
  $

  $
    [f_* V, f_* W] = f_* V((f_* W)^alpha) - f_* W((f_* V)^alpha)
    =\
    (partial f^beta) / (partial x^i) v^i partial /
    (partial y^beta) (f_* W)^alpha -
    (partial f^beta) / (partial x^i) w^i partial /
    (partial y^beta) (f_* V)^alpha = \
    v^i (partial) / (partial x^i) ((partial f^alpha) /
      (partial x^j) w^j) -
    w^i (partial) / (partial x^i) ((partial f^alpha) /
      (partial x^j) v^j) = \
    v^i (partial^2 f^alpha) / (partial x^i partial x^j) w^j +
    v^i (partial f^alpha) / (partial x^j) partial / (partial x^i) w^j -
    w^i (partial^2 f^alpha) / (partial x^i partial x^j) v^j +
    w^i (partial f^alpha) / (partial x^j) partial / (partial x^i) v^j =\
    (partial f^alpha) / (partial x^j) (v^i (partial w^j) /
      (partial x_i) - w^i (partial v^j)/ (partial x^i)) =
    (partial f^alpha) / (partial x^j) (V(w^j) - W(v^j)) = \
    (partial f^alpha) / (partial x^j) ([V,W]^j) = (f_* [V,W])^alpha
  $
]

*Пример* $RR^2 = {(x,y)}$

$
  V = (x^2 + y^2, 0)\
  W = (1,1)
$

$
  (R_alpha) : cases(
    tilde(x) = x cos alpha - y sin alpha,
    tilde(y) = x sin alpha + y cos alpha
  )
$

$
  [V,W]^1 = -2(x+y)\
  [V,W]^2 = 0
$

$
  (R_alpha)_* V = vec(
    cos alpha (tilde(x)^2 + tilde(y)^2),
    sin alpha(tilde(x)^2 + tilde(y)^2)
  ) \
  (R_alpha)_* W = vec(
    cos alpha - sin alpha,
    sin alpha + cos alpha
  )
$

$
  [f_* V, f_* W]^1 = -2 (cos alpha - sin alpha) cos alpha tilde(x) -
  2(sin alpha + cos alpha) cos alpha tilde(y)
$

$
  [f_* V, f_* W]^2 = -2 (cos alpha - sin alpha) sin alpha tilde(x) -
  2(sin alpha + cos alpha) sin alpha tilde(y)
$

$
  (R_alpha)_* [V, W] = vec(
    -2 cos alpha (x+y),
    -2 sin alpha (x+y),
  )
$

#theorem[][
  $V, W$ - в.п. на $M$. $V$ - генератор $psi(t, x)$

  Тогда
  #num_eq(
    $
      [V, W]|_x = lim_(t->0) 1/t [W|_x - (psi_t)_* W|_x]
    $,
  )

  $
    (psi_t)_* W|_x f(x)
  $

  #num_eq(
    $
      F_* V(f) = V(f(F(x)))
    $,
  )

  _Доказательство_ равенства 2
  $
    F : {y^alpha = F^alpha (x^i)}\
    (partial F^alpha)/ (partial x^i) v^i (partial f) / (partial y^alpha)\
    v^i (partial f) / (partial y^alpha) (partial F^alpha)/
    (partial x^i)
  $

  _Доказательство_

  $
    (psi_t)_* W|_x f(x) = ?
  $

  $
    (psi_t)_* W|_(psi_t (x)) f(psi_t (x)) =
    W|_x f(psi_t (x))\
    x --> psi_(-t) (x)\
    (psi_t)_* W|_x f(x) = W|_(psi_(-t) (x)) f(x)\
    f(x) = f(psi_(-t)(x)) + t V f(psi_(-t) (x)) + dots
  $

  $
    (psi_t)_* W|_x f(x) = W|_(psi_(-t)(x)) (f(psi_(-t)(x)) +
      t V f(psi_(-t)(x)) + t^2 g)
  $

  $
    lim_(t->0) 1/t [W f(x) - W|_(psi_(-t)) (x) f psi_(-t) (x)
      -t W_(psi_(t-)) (x) (V f(psi_(-t) (x)))] =
    lim_(t->0) [t
  $
]

#conseq[
  $
    (psi_s)_* [V,W] = - d / (d t)|_(t=s) ((psi_t)_* W)
  $

  _Доказательство_

  $
    (psi_s)_* [V,W] = [(psi_s)_* V, (psi_s)_* W] =
    [V, (psi_s)_* W] = lim_(t->0) 1/t [(psi_s)_* W -
      (psi_t)_* (psi_s)_* W] =\
    - d / (d t) |_(t=s) ((psi_t)_* W)
  $
]

#conseq[
  $V, W$ - генераторы поток соотв. $psi_t, psi_s$

  $psi_t, psi_s$ коммутируют $<==> [V, W] = 0$

  _Доказательство_
  1. $==>$
  $
    (psi_t)_* W = d / (d t) (psi_t phi_s psi_(-t)) = d / (d t)
    psi_s = W ==> d / (d t) \_(t = s) (psi_t)_* W = 0\
  $
]

