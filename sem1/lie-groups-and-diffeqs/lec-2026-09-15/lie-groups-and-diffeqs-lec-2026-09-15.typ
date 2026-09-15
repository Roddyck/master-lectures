#import "template-lec.typ": conf, definition, num_eq, theorem
#show: doc => conf([Группы Ли и ДУ. Лекция (15.09.2026)], doc)

$V$ - полное $<-->$ поток

#definition([
  $M$ - многообразие, $V$ - гладкое неполное векторное поле.
  $U subset RR times M, U in tau_(RR) times tau_(M),
  U supset {0} times M$

  $
    phi: U --> M
  $

  1. $phi(0, x) = x, quad forall x in M$
  2. $phi(t, phi(s, x)) = phi(t + s, x), quad forall t,s,x$
    для которых определены $phi(t, phi(s, x)), phi(t + s, x)$

  Тогда говорят, что на $M$ задана локальная 1-параметрическая
  группа преобразований
])

#theorem(1, [
  $forall$ системы ОДУ 1-го порядка вида
  $
    (d x^(alpha)) / (d t) = V(x^1, dots, x^n)
  $

  $exists !$ локальный поток $phi(t, x)$ для которого $V$ является
  генератором

  Доказательство в курсе ОДУ
])


#block(
  stroke: black,
  inset: 1em,
  width: 100%,
)[
  *Замечание*. Th. 1 называется 1-ая теорема Ли
]

#theorem(2, [
  $V$ - в.п. на $M$, $phi: M --> M$ - диффеоморфизм,
  $V$ - генератор потока $psi(t, x)$

  Тогда $phi_* V$ - генератор потока $phi psi phi^(-1)$

  _Доказательство_

  $
    phi_* V |_(phi(x)) = (d phi(psi(t, x))) / (d t) |_(t = 0)
  $

  $
    phi_* V |_(x) = (d phi(psi(t, phi^(-1)(x)))) / (d t) |_(t = 0)
  $

  $phi psi_t phi^(-1)$ - локальный поток ?

  $
    phi psi_0 phi^(-1) = phi id phi^(-1) = phi phi^(-1) = id
  $

  $
    phi psi_t phi^(-1) phi psi_s phi^(-1) = phi psi_t psi_s
    phi^(-1) = phi psi_(t + s) phi^(-1)
  $
])

#block(
  stroke: black,
  inset: 1em,
  width: 100%,
)[
  *Следствие*. $V$ - генератор потока $psi_V (t, x)$. Поле
  $V$ инвариантно относительно $phi: M --> M$ - дифф-м $<==> phi$
  и $psi_V (t, x)$ коммутируют

  _Доказательство_
  $
    (d psi^i) / (d t) (t, x) = V^i (psi^1, dots, psi^n) equiv
    (d x^i) / (d t) = V(x^1, dots, x^n)
  $

  1. $==>$
  $
    phi_* V = V ==> phi psi(t, phi^(-1)(x)) = psi(t, x), quad
    x --> phi(x)
  $

  $
    phi psi = psi phi
  $

  2. $<==$
  $
    phi psi = psi phi \
    phi psi_t phi^(-1)= psi_t ==> phi_* V = V
  $
]

*Пример*
$V = (x, y)$ на $RR^2, quad T_arrow(a), quad arrow(a) = (alpha, beta)$

Найдем поток $psi(t, x)$ с генератором $V$

$
  cases(
    (d psi^1) = psi^1,
    (d psi^2) = psi^2,
    psi^i (0) = x^i
  )
$
$
  cases(
    psi^1 = c_1 e^t,
    psi^2 = c_2 e^t
  )
$
$
  cases(
    psi^1 (0) = x,
    psi^2 (0) = y
  )
$

$
  cases(
    psi^1(t,x,y) = x e^t,
    psi^2(t,x,y) = y e^t
  )
$

$
  psi T_(arrow(a)) : cases(
    tilde(x) = (x + alpha) e^t,
    tilde(y) = (y + beta) e^t,
  )
$

$
  T_(arrow(a)) psi : cases(
    tilde(x) = x e^t + alpha,
    tilde(y) = y e^t + beta,
  )
$

2. Проверим $(T_a)_* = V$

*Пример*
$V = (x, y)$ на $RR^2$
$
  R_alpha : cases(
    tilde(x) = x cos alpha - y sin alpha,
    tilde(y) = x sin alpha + y cos alpha
  )
$

$
  psi : cases(
    tilde(x) = x e^t,
    tilde(y) = y e^t,
  )
$

$
  R_alpha psi = psi R_alpha
$

#theorem([3 (Лемма Адамара)], [
  Пусть $f(t,x) : M times RR --> RR$ \
  $f(0, x) = 0 quad forall x in M ==> exists g(t, x) |
  f(t,x) = t g(t, x), quad g(0,x) = (d f) / (d t) |_(t = 0)$

  _Доказательство_

  Пусть $g(t,x) = integral_(0)^1 (d f) / (d t) (s t, x) d s$
  $
    t g(t,x) = integral_(0)^1 (d f) / (d t) (s t, x) d (t s) =
    integral_0^1 d z (d f) / (d z) (z, x) = f(t,x) - f(0,x) =
    f(t,x)
  $
])

#theorem(4, [
  $V$ - генератор потока $psi(t, x) ==> forall f: M --> RR quad
  exists g_1 (t,x) |$
  #num_eq(
    $
      f(psi(t, x)) = f(x) + t V(f)(x) + t^2 g_1
      (t,x)
    $,
  )

  _Доказательство_

  Пусть $g(t,x) = f(psi(t, x)) - f(x)$
  $
    g(0,x) = 0 ==> exists tilde(g) | g = t tilde(g),\
    tilde(g)(0,x) = (d g) / (d t)|_(t=0)
  $

  $
    d / (d t)|_(t=0): f(psi(t, x)) - f(x) = t tilde(g)
  $

  $
    V(f)(x) = tilde(g)(0,x)
  $

  $
    tilde(g)(t,x) - V(f)(x)|_(t=0) = 0 ==> exists g_1 | g_1(t,x)
    - V(f)(x) = t g_1
  $

  $
    f(psi(t, x)) - f(x) = t(V(f)(x) + t g_1)\
    f(psi(t, x)) = f(x) + V(f)(x) + t^2 g_1
  $
])

#block(
  stroke: black,
  inset: 1em,
  width: 100%,
)[
  *Замечание*.
  #num_eq(
    $
      f(psi(t, x)) = f(x) + t V(f)(x) + t^2 / 2 V^2 (f)(x) + dots +
      t^n / n! V^n (f)(x) + t^(n+1) g^(n+1)
    $,
  ) <eq-2>
]

#definition[
  Равенство @eq-2 называется рядом Ли для $f(x)$ относительно
  потока $psi(t, x)$
]

#definition[
  Скобкой Ли или коммутатором векторных полей $V, W$ называют
  векторное поле удовлетв. условию
  $
    [V, W] (f) = V(W(f)) - W(V(f))
  $
]

*Задача* Пусть $V=(v^i), W=(w^i)$.

Найти координаты поля $[V, W]$
