#import "template-lec.typ": *
#show: doc => conf([Диффуры. Лекция (25.09.2026)], doc)

$f_1 (x), f_2 (x) : [x_0 - h, x_0 + h] --> RR$ - липшицевы.
$a_1 f_1 + a_2 f_2 quad forall a_1, a_2 in RR$ - липшицева ?

$
  exists M_1 thick forall x_1, x_2 quad |f_1(x_1) - f_1(x_2)|
  < M_1 |x_1 - x_2|
$

$
  |(a_1 f_1 + a_2 f_2)(x_1) - (a_1 f_1 + a_2 f_2)(x_2)|
  <= |a_1| |f_1(x_1) - f_1(x_2)| +
  |a_2| |f_1(x_1) - f_1(x_2)| <=\
  (|a_1| M_1 + |a_2| M_2) |x_1 - x_2|
$

#num_eq(
  $
    cases(
      dot(X) = F(t,x),
      X(t_0) = X_0
    )
  $,
) <prob-1>


#num_eq(
  $
    cases(
      dot(X)_n = F_n (t,x),
      X(t_n) = X_n
    )
  $,
) <prob-2>

#theorem[][
  ${F_n (t, X)}_(n >= 0)$ - непр, $R = {(t,X) : t_0 <= t <= t_0 + a,
    ||X-X_0|| <= b}$\
  $
    F_n (t,X) arrows_(n->+oo)^R F_0 (t, X)
  $

  $X_n (t)$ - решение @prob-2 на $[t_0, t_0+a]$
  $
    t_n --> t_0 quad X_n -->_(n -> +oo) X_0
  $

  $
    exists X_(n_1), X_(n_2), dots \
    X_0 (t) = lim_(k -> oo) X_n_k (t) - "решение при" n = 0
  $

  Если задача Коши @prob-2 при $n=0$ имеет един. решение тогда сходимость
  равномерная

  _Доказательство_

  $
    exists K > 0 : ||F_n (t,X)|| <= K quad forall (t,X) in R
  $

  $
    ||dot(X)_n (t)|| <= K ==> forall t', t'' in [t_0, t_0+a]\
    ||X_n (t') - X_n (t'')|| <= K dot |t' - t''| quad forall n in NN\
    ||X_n (t) - X_0|| <= b
  $

  Тогда выполняется теорема Арцелла для $X_n ==> {X_n_k}_(k>=1)$ -
  равномерю сх на $[t_0, t_0+a]$

  $
    F_(n_k) (t, X_(n_k) (t)) arrows_(k->oo)^([t_0, t_0 + a]) F_0 (t, X)\
    X_(n_k) (t) = X_(n_k) + integral_(t_0)^(t) F_(n_k) (s, X_(n_k) (s)) d s
  $

  #num_eq(
    $
      X_0 (t) = X_0 + integral_(t_0)^t F_0 (s, X_0 (s)) d t
    $,
  )

  Тогда $X_0$, по теореме о существовании решения, является
  решением @prob-2 при $n = 0$

  Если решение единтсвенно, тогда любая такая последовательность
  будет равномер сх к $X_0$
]

#theorem[Кнезера][
  Пусть есть задача Коши @prob-1 на $R$, $t in [t_0, t_0 + a]$
  $
    ||F(t,X)|| <= M, quad h = min{a, b/M}\
    forall c in [t_0, t_0 + h]\
    S_c = {X_c : [t_0, c] thick exists "решение"} - "множество достижимости"
  $

  $S_c$ - континум (связный компакт)

  _Доказательство_

  $
    Sigma " - множество решений"\
    [t_0, c] subset [t_0, t_0 + h]\
    S_c = {X(c) : X(t) in Sigma}
  $

  $
    forall X_(n, c) in S_c, thick lim_(n->oo) X_(n,c) = X_c ==>^? X_c =
    X(t)|_(t=c) <==> X(t) in Sigma
  $

  $
    {X_n (t)} : X_n (c) = X_(n,c)
  $

  ${X_n (t)}$ удовл. условиям теоремы Арцелла

  $exists X_(n_k) (t) arrows X(t) in Sigma$

  $
    X(c) in S_c
  $

  Тогда $S_c$ - ограничено, а тогда и компактно

  $
    {X_n (t)} arrows_(n->oo)^([t_0, c]) X(t)
  $

  Пусть $S_c$ не связно
  $
    S_c = S^0 union S^1 quad S^0 inter S^1 = emptyset
  $

  $S^i$ - замкнутые

  $
    delta = "dist" (S^0, S^1) > 0 \
    e(X) = "dist" (X, S^0) - "dist" (X, S^1)
  $

  1. $X in S^1 => e(X) >= delta > 0$
  2. $X in S^0 => e(X) <= -delta < 0$
  $e(X) != 0$

  $
    forall epsilon > 0 quad X(t) in Sigma
  $

  $exists$ непрерывная $G(t, X)$ удов. условиям:

  1. $||G(t,X)|| <= M + epsilon$
  2. $||F(t,X) - G(t,X)|| < epsilon$
  3. $G$ - липш. по $X$
  4. $X = X(t)$ - решение задачи Коши #num_eq($X=G(t,x), X(t_0) = X_0$)

  При этом для того, чтобы удовлетворялось условие 3 достаточно
  взять непрерывно дифференцируемую функция из $U_epsilon (F)$

  $G^* (t,X)$ - удовл 1-3, $M + epsilon = M$ в 1., в 2. $epsilon = epsilon/2$
  #num_eq(
    $
      G(t,X) = G^star (t,X) + (F(t,X) - G^star (t, X(t)))\
    $,
  )

  $
    ||G(t,X) - G^star (t,X)|| <= ||F(t,X) - G^star (t, X(t))|| < epsilon/2
  $

  Тогда $G$ удов. 1-3

  $
    G(t, X(t)) = F(t, X(t)) = dot(X)(t)
  $

  $
    X = X_0 (t), thick X = X_1 (t) in Sigma
  $

  $
    X_0 (c) in S^0, X_1 (c) in S^1\
    G_0 (t,X), G_1 (t,X) thick (1-4)
  $

  Построим семейство решений задач Коши
  #num_eq(
    $
      dot(X) = G_(theta) (t,X), thick X(t_0) = X_0, thick theta in [0,1]
    $,
  )

  #num_eq(
    $
      G_(theta) (t,X) = theta G_1 (t, X) + (1-theta) G_0 (t, X)
    $,
  )

  $G_theta$ - липшицева. Тогда $exists !$ решение $X=X(t, theta)$.
  Тогда в силу теоремы Пекара при любом $b$ решение $X=X(t,theta)$
  $exists !$ на $[t_0, c]$
  $
    ||G_theta (t,X)|| <= theta ||G_1 (t,X)|| + (1-theta) ||G_0 (t,X)|| <=
    (M + epsilon) ==>\
    ==> ||X(t,theta) - X_0|| <= (M + epsilon) dot h ==>
  $

  $
    X(t, theta) arrows_(t -> theta_0)^([t_0, c]) X(t, theta_0)
  $

  $X(c, theta) in C^0$ по $theta$

  $
    e(X(c, theta)) in C^0
  $

  Тогда по построению
  $
    e(X(c, theta)) = cases(
      < 0 comma quad theta = 0,
      > 0 comma quad theta = 1,
    )
  $

  $
    exists eta in (0, 1) : e(X(c,eta)) = 0
  $

  Выбор $eta$ зависит от $epsilon$. $eta = eta(epsilon)$
  $
    epsilon = 1/n, quad G_n (t,X) = G_(1/n) (t,X)
  $

  $
    ||F(t,X) - G_n (t,X)|| <= 1/n
  $

  $eta = theta$

  #num_eq(
    $
      dot(X) = G_(1/n) (t,X), quad X(t_0) = X_0
    $,
  )

  имеет един. решение $X=X_n (t)$ на $[t_0, c]$.

  $
    exists X_(n_k) arrows_(n->oo)^([t_0, c]) X(t) \
    ||X_n (t) - X_0|| <= b
  $

  решение $exists$ на $t_0 <= t <= min{c, t_0 + b / (M + 1/n)}$

  $
    min{c, t_0 + b / (M + 1/n)} -->_(n->oo) c
  $

  Тогда $X(t)$ решение задачи Коши
  $
    e(X(c)) = lim_(n->oo) e(X_n (c)) = 0 ==>
    X(c) in S^0 inter S^1
  $
  #qedsymbol
]

*Задача*
Доказать теорему Кнезера для одномерного случая

$
  dot(x) = F(t, x)\
  x(t_0) = x_0
$

$
  F - C^0 (R) quad R = [t_0, t_0 + h] times overline(U_b (x_0))\
  |F(t,x)| < M
$

$
  S_c = {x_c = x(c) : x(t) "- решение"}\
  S_c = [alpha, beta] subset RR
$

0. $S_c$ - огр
$
  x(t) = x_0 + integral_(t_0)^t F(s, x(s)) d s\
  |x(t) - x_0| = |integral_(t_0)^t F(s, x(s)) d s| <=
  |integral_(t_0)^t |F(s, x(s)) d s| | <= M |t_0 - t| <= M h <= b
$
1. $S_c$ - замкн
$
  x_n (c) = x_(n,c) in S_c
$

$
  F(t, x_n) --> F(t,x)
$
в частности при $t = c$
$
  ==> x_(n,c) = x_n (c) --> x_c ==> x(t) in Sigma
$
