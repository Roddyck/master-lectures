#import "template-lec.typ": *
#show: doc => conf([Дискретные системы (18.09.2026)], doc)

$
  f in C^r (m), quad dim M < +oo, M - "компакт"\
  M = [a,b], quad f : [a,b] -> [a,b]\
  underline(r = 0) quad ||f||_(C^0) = sup_(x in M) ||f(x)||_M\
  underline(r >= 1) quad ||f||_(C^1) = max{||f||_(C^0), ||D f||_(C^0)}\
  ||f||_(C^r) = max{||f||_(C^0), ||D f||_(C^0),dots, ||D^r f||_(C^0)}
$

$C^r (M), r >= 0, C^r (M)$ - полно.

$M = [a,b]$

$forall {f_n (x)}$ - фундаменатальна
$
  forall epsilon > 0 thick exists N_epsilon in NN | forall n,m
  > N_epsilon quad ||f_n - f_m||_(C^0) < epsilon \
  epsilon > ||f_n - f_m||_(C^0) = sup_(x in [a,b]) |f_n (x) - f_m (x)|
  >= |f_n (x) - f_m (x)| forall x in [a,b] <==>\ f_n(x)
  arrows_(n->oo)^([a,b]) f_* (x) in C^0 [a,b]
$


$
  epsilon > ||f_n - f_m||_(C^1) = max{sup|f_n - f_m|, sup |f'_n - f'_m|} >=
  max(|f_n - f_m|, |f'_n - f'_m|)
$

$
  |f_n - f_m|, |f'_n - f'_m| < epsilon quad forall x in [a,b]
$

$
  {f_n} arrows f_* (x) \
  {f'_n} arrows phi(x) \
  ==> f_* (x) in C^1 [a,b], f_* (x) = phi(x) thick forall x in [a,b]
$

*Контрольный вопрос*: доказать полноту для всех $C^r$

$
  B^r_epsilon (f) = {g in C^r (M) : ||f - g||_(C^r) < epsilon}
$

1. Типичное свойство д.д.с
  1. всюдо плотное множество -- $overline(B) = A$
  2. граничное множество -- $overline(A-B) = A$
  3. нигде не плотное множетсво -- $overline(A backslash overline(B)) = A$
  4. множество 1-ой категории -- $B = union.big_(n=1)^oo B_n$ - нигде не плотные
  5. множество 2-ой категории (массивное мн-во) -- дополнительное к мн-ву 1-ой категории
    Массивное мн-во -- мн-во представимое в виде счетного пересеч.
    всюдо плотных


#theorem([Бэра о категории], [
  Люьое множество $B = union.big_(n=1)^oo B_n$ - нигде не плотные,
  $B subset M$, $M$ - полное метр. Тогда $B$ - граничное множество.

  Другими словами, всякое полное метрическое пространство не является
  множетсвом 1-ой категории.
])

Полное метрическое пространство имеет мощность континуума
