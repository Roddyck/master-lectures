#import "template-lec.typ": *
#show: doc => conf([Диффуры. Лекция (18.09.2026)], doc)

= Теорема о продолжении решения задачи Коши

#num_eq(
  $
    cases(
      dot(X) = F(t,x),
      X(t_0) = X_0
    )
  $,
) <prob-1>

#conseq[
  $
    F in C^0_(E subset RR^(n+1)), ||F|| <= M
  $

  $E_0 subset E$ - компакт, $E$ - огр. и открытое, $F$ - огр.

  $exists h = h(E, E_0, M), quad forall (t_0, X_0) in E_0$, то задача
  Коши @prob-1 имеет решение и каждое решение существует на отрезке $[t_0 -h,
    t_0 + h], quad h = min{a, a/M}, thick a = rho(E_0, partial E)$
]

#definition[
  Пусть $F$ - непрерывна по совокупности $t, X$ на $E$, $X = X(t)$
  решение задачи Коши @prob-1 на промежутке $j$.

  $j$ называется правым (левым) максимальным интервалом существования решения,
  если не существует продолжения $X_("ext") = X_("ext") (t)$ на
  $j_1 supset j med (j_1 != j) | j_1$ имеет общую левую (правую)
  границу с $j$.

  $j$ - максимальные, если он и правый и левый максимальный
]

#theorem(1, [
  Пусть $F$ - непр на $E$, которое открыто, $X = X(t)$ - решение @prob-1
  на интервале $j$

  Тогда $X(t)$ может быть продолжено как решение задачи @prob-1 на
  макс. интервал существования $(omega_(-), omega_+)$ при этом
  $X(t) -->_(t -> omega_- (omega_+)) partial E$

  $
    X(t) --> partial E
  $

  1. $X(t) --> oo$ либо
    $X(t)$ не содержится ни в какой компактной подобласти $E$

  _Доказатеьльство_

  Рассмотрим исчерпание области $E$ множествами $E_1 subset E_2 subset
  dots subset E_(n) subset dots$
  $
    E = union.big_(n=1)^oo E_(n), \
    forall n >= 1 quad overline(E_n) subset E_(n+1)\
    overline(E_n) - "компакт"
  $

  Возьмем точку $(t_0, X_0) in E$ тогда $forall n >= 1 thick exists
  epsilon_n
  > 0 : (t_0, X_0) in overline(E_n)$ тогда все решения @prob-1, которые
  проходят через $(t_0, X_0)$ на интервал $[t_0 - epsilon_n,
    t_0 + epsilon_n]$

  $forall X = X(t), quad t in [a , b_0]$. Точка $(b_0, X(b_0)) in
  overline(E)_(n_(1))$, тогда это решение можно продолжить на
  $[b_0, b_0 + epsilon_(n_1)]$. Точка $(b_0 + epsilon_n_1, X(b_0 + epsilon_n_1))
  in overline(E)_(n_(1))$, тогда это решение можно продолжить на
  $[b_0, b_0 + 2 epsilon_(n_1)]$ и т.д.

  Т.к. $E_n_1$ - компакт, то продолжная процесс мы достигнем точку
  $b_1 = b_0 + j_1 epsilon_n_1$, $(b_1, X(b_1)) in.not E_n_1 ==>
  exists n_j : (b_1, X(b_1)) in E_n_j quad (j > j_1)$

  Повторая указанные рассуждения мы указываем последовательность
  $n_1 < n_2 < dots < n_j < dots$ и посл-ть точек
  $b_0, b_1, dots, b_j, dots$ \
  $b_0, b_1, dots, b_j in [a, omega_+), quad omega_+ = lim_(j->oo) b_j$

  $(b_j, X(b_j)) in.not overline(E)_n_j$

  $
    t --> omega_+, quad t in [a, omega_+)
  $

  Остается проверить, что никакая точка $overline({(b_j, X(b_j))})
  in.not "int" E$. В обратном случае найдется элемент исчерпания
  $E$, но тогда по следствию можно построить продолжение решения
  через некоторую предельную точку ${(b_j, X(b_j))}$.

  Тогда построили
  $
    X(t) -->_(t -> omega_+) partial E
  $

  Если добавить условие того, что $F$ - огр. на пересечении $E$ и
  какой-либо окр-ти $(delta, X_0)$, и $exists F(delta, X_0) :
  F(t, X)$ - непр. в $delta, X_0)$, то тогда $X(t) in C^1 [a, delta]$

  $X(t)$ имеет продолжение на $[a, omega_+]$, $X(t) --> partial E$
  #qedsymbol
])

#conseq[
  $F in C^0 (overline(E))$, @prob-1 имеет решение на $j$ - правом макс.
  интервале существования.

  1. $j = [t_0, +oo)$
  2. $j = [t_0, delta) quad (delta < +oo)$ \
    $(delta, X(delta)) in partial E$
  3. $j = [t_0 ,delta), quad ||X(t)|| -->_(t-> delta - 0) oo$
]

= Теорема о структуре множества достижимости решения задачи Коши (Теорема Кнезера)

#num_eq(
  $
    cases(
      dot(X) = F_n(t,x),
      X(t_n) = X_n
    )
  $,
) <prob-2>

#theorem([], [
  $
    X in RR^n \
    {F_n(t, X)}_(n >= 0) subset C^0_R\
    F_n (t, X) ==>^(RR^n)_(n -> +oo) F_0 (t, X)\
    X_n -->_(t_n ->_(n -> oo) t_0) X_0
  $

  Тогда
  $
    exists X_n_1 (t), X_(n_2) (t), dots, X_(n_k) ==>^([t_0, t_0+a])_(k->oo)
    X_0(t)
  $

  #num_eq(
    $
      cases(
        dot(X) = F_0(t,x),
        X(t_0) = X_0
      )
    $,
  ) <prob-lim>

  Если решение @prob-lim единственно, тогда
  $
    lim X_n (t) = X_0 (t) - "равномерно на " [t_0, t_0 + a]
  $
])

*Задача*
$
  dot.double(X_n)(t) <= M\
  dot(X)_n (t) <= M_1
$

доказать, что ${X_n (t)}_(n >= 0)$ - предкомпактна в $C^1$ норме

Покажем, что ${dot(X)_n (t)}_(n >= 0)$ - предкомп. в $C^0$

$
  forall t in [a, b], t' in [a,b] quad |dot(X_n) (t) - dot(X_n) (t')|
  <= |dot.double(X)| (xi) dot |t - t'| <= M |t - t'| < epsilon \
  ==> |t-t'| < epsilon / M = delta
$

$
  {X_n_k}_(k>=0) arrows X_* (t) "in" C^0\
$
