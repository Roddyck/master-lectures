#import "template-lec.typ": *
#show: doc => conf([Функан (28.09.2026)], doc)

*Вопрос*\
Существует ли неограниченный линейный функционал на $H$

#theorem[(Рисса)][
  $
    forall T in H^* thick exists ! y in H : T(x) = (y, x) quad forall x in H
  $
  и при этом
  $
    ||T||_(H^*) = ||y||_H
  $

  _Доказательство_
  $
    N = ker T = {x | T(x) = 0}
  $
  Если $T(x) = 0 thick forall x in H ==> N = H, thick T(x) = (0, x)$

  Пусть $N != H$.

  в $N^tack.t$
  $
    exists 0 != x_0 : T(x_0) != 0
  $

  Рассмотрим
  $
    y = (T(x_0)) / (||x_0||^2) x_0\
    T(alpha x_0) = alpha T(x_0)\
    (y, alpha x_0) = alpha (y, x_0)
  $

  $
    ||T|| = sup_(||x|| = 1) |T(x)| = sup_(||x|| = 1) = |(y,x)| <=
    sup_(||x|| = 1) ||y|| ||x|| = ||y||
  $
  $
    ||T|| = sup_(||x|| = 1) |T(x)| >= |T(y / (||y||))| = (y, y / (||y||)) =
    (||y||^2) / (||y||) = ||y||
  $
  #qedsymbol
]

#definition[
  $
    a(dot, dot) : H times H --> RR
  $
  называется билинейной, если
  $ a(lambda u + mu v, w) = lambda a(u, w) + mu a(v, w)\
  a(u, lambda v + mu w) = lambda a(u, v) + mu a(u, w) $.

  Билинейная форма называется:
  1. Симметричной, если $a(u,v) = a(v,u)$
  2. Ограниченной, если $|a(u,v)| <= a^* ||u|| dot ||v||$
  3. Коэрцитивной, если $exists a_* > 0 : a(u,u) >= a_star ||u||^2$
]

*Задача 1*
Найти $u in H : a(u,v) = l(v) forall v in H$

#lemma[Лакса-Мильграма][
  $H$ - г.п., $l$ - лин.огр. функционал, $a$ - билинейная, огр. коэрцитивная форма

  Тогда задача 1 имеет единственное решение $u in H$

  _Доказательство_

  Пусть $(u,v)_a = a(u,v), quad H_a = (H, (dot, dot)_a)$
  $
    ||u||_a = sqrt((u,u)_a) = sqrt(a(u,u)); quad d_a (u,v) = ||u-v||_a
  $

  Рассмотрим фундаментальную посл-ть ${u^n}_(n>=1)$

  $
    ||u^k - u^m||_a -->_(k,m -> oo) 0
  $
  $
    0 <-- ||u^k - u^m||_a = sqrt(a(u^k - u^m, u^k - u^m)) >= sqrt(a_star)
    ||u^k - u^m|| >= 0 \
    ||u^k - u^m|| -->_(k,m -> oo) 0 \
    ==> exists u^oo in H : ||u^oo - u^n|| -->_(n->oo) 0
  $

  $
    ||u^oo - u^n||_a -->_(n->oo) 0
  $

  $
    0 <= ||u^oo - u^n||_a = sqrt(a(u^oo - u^n, u^oo - u^n)) >= sqrt(a_star)
    ||u^oo - u^n|| --> 0\
    ==> u^oo in H
  $

  $
    |l(u)| <= ||l|| dot ||u|| <= (||l||)/(sqrt(a_star)) sqrt(a(u,u)) =
    (||l||)/sqrt(a_star) ||u||_a
  $

  По теореме Рисса
  $
    exists ! u in H : (u,v)_a = l(v) quad forall v in H_a
  $
]

*Упражнение*
Доказать, что в конечномерном случае любой лин функц. - огр.

*Упражнение*
Доказать, что в конечномерном случае любая билин. форма - огр.

*Упражнение*
Доказать, что в конечномерном случае любая пол. определенняа билин. форма - коэрцитивна.

*Задача 2*

$a : H times H --> RR$ - билинейная, $l : H --> RR$ - лин.
$
  I(u) = 1/2 a(u,u) - l(u)
$

Найти $u in H$
$
  I(u) --> min
$

#theorem[][
  Пусть $H$ - лин. пр-во, $l$ - лин. функционал, $a$ - билин. симм. неотр. опр. форма

  Тогда задачи 1 и 2 эквивалентны

  _Доказательство_

  $u_0 in H$ - решение задачи 2
  $
    I(u_0 + lambda v, u_0 + lambda v) >= I(u_0, u_0) quad forall lambda in RR, v in H
  $

  $
    1/2 a(u_0 + lambda v,u_0 + lambda v) - l(u_0 + lambda v) >= 1/2 a(u_0,u_0) - l(u_0)\
    1/2 a(u_0, u_0) + lambda/2 a(u_0, v) + lambda/2 a(v, u_0) + lambda^2/2 a(v,v) - l(u_0) - lambda l(v)
    >=1/2 a(u_0,u_0) - l(u_0)
  $

  $
    (a(v,v)) / 2 lambda^2 + lambda(a(u_0,v) - l(v)) >= 0
  $

  1. $a(v,v) = 0 ==> a(u_0,v) - l(v) = 0$
  2. $a(v,v) != 0 ==> (a(u_0, v) - l(v))^2 <= 0 ==> a(u_0,v) - l(v) = 0$

  $u_0 in H$ - решение задачи 1\
  Проводим рассуждения в обратную сторону
]

= Метод Ритца

#definition[
  $H^N subset H$, ${phi_1, dots, phi_N}$ - базис

  Найти $u^N in H$
  $
    I(u^N) --> min
  $
  $
    I(u^N) = 1/2 a(u^N,u^N) - l(u^N)
  $

  $u^N$ - приблежённое решение
]

$
  u^N = c_1 phi_1 + dots + c_N phi_N \
  c = vec(c_1, dots.v, c_N) in RR^N
$

$
  I(u^N) = 1/2 a(sum_(i = 1)^N c_i phi_i,sum_(j = 1)^N c_j phi_j) -
  l(sum_(i = 1)^N c_i phi_i) --> min
$

$
  I(u^N) = sum_(i=1)^N sum_(j=1)^N (c_i c_j)/2 a(phi_i, phi_j) - sum_(i=1)^N
  c_i l(phi_i) --> min
$

$
  cal(F) (c_1, dots, c_N) --> min
$

$
  (partial cal(F)) / (partial c_i) = 0 quad forall i = 1, dots, N
$

$
  (partial cal(F)) / (partial c_k) = sum_(j=1)^N c_j / 2 a(phi_k, phi_j)
  + sum_(i=1)^N c_i / 2 a(phi_i, phi_k) - l(phi_k) = 0
$

$
  sum_(i=1)^N a(phi_k, phi_i) c_i = l(phi_k)
$

В условиях теоремы Лакса-Мильграма
$
  mat(
    a(phi_1, phi_1), dots, a(phi_1, phi_m), dots, a(phi_1, phi_N);
    dots, dots, dots, dots, dots;
    a(phi_n, phi_1), dots, a(phi_n, phi_m), dots, a(phi_n, phi_N);
    dots, dots, dots, dots, dots;
    a(phi_N, phi_1), dots, a(phi_N, phi_m), dots, a(phi_N, phi_N);
  )
$

$
  D_1, dots, D_N\
  cases(
    D_1 a(phi_1, phi_1) + D_2 a(phi_2, phi_1) + dots + D_N a(phi_N, phi_1) = 0,
    dots,
    D_1 a(phi_1, phi_N) + D_2 a(phi_2, phi_N) + dots + D_N a(phi_N, phi_N) = 0,
  )
$

$
  a(D_1 phi_1 + dots + D_N phi_N, D_1 phi_1 + dots + D_N phi_N) = 0\
  ==> D_1 phi_1 + dots + D_N phi_N = 0
$

Найти $u in H$
$
  a(u,v) = l(v) quad forall v in H\
  u --> sum_(i=1)^N c_i phi_i\
  v --> phi_1, dots, phi_N
$

#theorem[][
  $(X, d)$ - полное метр. пр-во, $B_n = {x in X | d(x, a_n) <= r_n}$

  $
    forall {B_n}_(n=1)^oo thick forall n in NN : B_(n+1) subset B_n, thick
    r_n -->_(n->oo) = 0 ==> exists ! x_0 in X thick x_0 in inter.big_(n=1)^oo B_n
  $

  _Доказательство_

  $
    {a_0, a_1, dots, a_n, dots }\
    forall p in NN quad B_(n+p) subset B_n ==> d(a_(n+p), a_n) <= r_n\
    lim_(n->oo) r_n = 0\
    d(a_(n+p), a_n) --> 0
  $
  т.е. ${a_n}$ - фунд.

  $
    exists lim a_n = a in X\
    k in NN : {a_k, a_(k+1), dots } subset B_k\
    forall n in NN quad a = lim a_n in B_n\
    a in inter.big_n B_n
  $

  Пусть
  $
    b in inter.big_n B_n thick b != a thick d(a,b) = delta > 0\
    a, b in B_n, quad d(a,a_n) <= r_n; thick d(b,a_n) <= r_n\
    delta = d(a,b) <= d(a, a_n) + d(a_n, b) <= 2 r_n\
    2 r_n --> 0 ==> delta <= 0
  $
]

#theorem[][
  $
    inter.big_n B_n != emptyset
  $
  Тогда $X$ - полное

  _Доказательство_

  Рассмотрим ${x_n}$ - фунд.
  $
    {x_(n_k)} quad forall p > 0 : rho(x_(n_(k+p)), x_(n_k)) < 1/2^k
  $
]

#definition[
  Множество 1-й категории
  $
    M = union_(n=1)^oo M_n,
  $
  где $M_n$ - нигде не плотны

  Множество 2-й категории - остальные
]

#theorem[Бэра][
  полное м.п. - мн-во 2 категории

  _Доказательство_
  Пусть
  $
    X = union_(n) M_n,
  $
  где $M_n$ - нигде не плотны

  $
    B_0 = B(a, 1)
  $

  т.к. $M_1$ нигде не плотно
  $
    B_1 subset B_0, thick r < 1/2, B_1 inter M_1 != emptyset
  $

  $
    M_2 : B_2 subset B_1, thick r < 1/2^2, B_2 inter M_2 != emptyset
  $

  $
    B_1 supset B_2 supset dots supset dots\
    r_n = 1/2^n --> 0
  $

  $
    a_0 in X\
    a_0 in inter.big B_n
  $

  $
    forall n in NN, thick a_0 in.not M_n\
    a_0 in.not union.big M_n
  $
]


#theorem[Банаха о неподвижной точке][
  Пусть $X$ - полное м.п. $f : X --> X$, $rho(f(x_1), f(x_2)) <= alpha rho(x_1, x_2), thick alpha < 1$

  Тогда
  $
    exists ! x in X quad f(x) = x
  $

  _Доказательство_

  Рассмотрим пос-ть итераций $x, f^1, f^2, dots; quad f^n = f(f^(n-1)), quad f^0 = x$

  $
    rho(f^2, f^1) <= alpha rho(f^1, x)\
    rho(f^3, f^2) <= alpha rho(f^2, f^1) <= alpha^2 rho(f^1, x)\
    dots\
    rho(f^(n+1), f^n) <= alpha^n rho(f^1, x)
  $

  $
    rho(f^(n+m), f^n) <= rho(f^(n+m), f^(n+m-1)) + dots + rho(f^(n+1), f^n) <=\
    (alpha^(n+m-1) + dots + alpha^n) rho(f^1, x) <= alpha^n (1 + dots + alpha^(m-1)) rho(f^1, x)
    <= alpha^n (1 / (1-alpha)) rho(f^1, x)
  $
]

= Проекционные методы

$
  - d / (d x) (p(x) (d u(x)) / (d x)) + q(x) u(x) = f(x) quad x in [0; l]\
  -alpha u'(0) + beta u(0) = mu_0\
  -gamma u'(l) + delta u(l) = mu_l\
$

$
  - d / (d x) (p(x) (d u(x)) / (d x)) + q(x) u(x) = f(x) quad x in [0; l] thick | v(x), integral_0^l\
  u(0) = 0\
  u(l) = 0
$

$
  integral_0^l d / (d x) (p(x) (d u(x)) / (d x)) dot v(x) d x + integral q(x) u(x) v(x) d x
  = integral_0^l f(x) v(x) d x\
  -p(x) u'(x) dot v(x)|_(0)^l + integral_0^l p(x) u'(x) v'(x) d x+ integral q(x) u(x) v(x) d x
  = integral_0^l f(x) v(x) d x\
$

$
  K = {u in C^1 ([0; l]), u(0) = u(k)}\
  v in K
$

Найти $u in K:$
$
  integral_0^l p(x) u'(x) v'(x) d x+ integral q(x) u(x) v(x) d x
  = integral_0^l f(x) v(x) d x\
  forall v in K
$

$
  & a(u,v) := integral_0^l p(x) u'(x) v'(x) d x+ integral q(x) u(x) v(x) d x \
  & l(v) := integral_0^l f(x) v(x) d x \
$
$
  a(u,v) = l(v)
$

$
  I(u) --> min, quad u in K, quad I(u) = 1/2 integral_0^l p(x) (u'(x))^2 d x
  + 1/2 integral_0^l q(x) u^2 d x - integral_0^l f u d x
$
