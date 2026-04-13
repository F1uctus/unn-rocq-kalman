(** remove printing * *)

(** * Лекция 7. Верификация поиска максимума в массиве (все доказательства). Зависимые суммы и квантор существования. Извлечение программ из конструктивных доказательств *)

Require Import Arith.
Require Import Lia.
Require Import Bool.
Import Nat Peano.

Global Hint Resolve ltb_spec0 leb_spec0 eqb_spec : bdestruct.

Ltac bdestr X H :=
  let e := fresh "e" in
   evar (e : Prop);
   assert (H : reflect e X); subst e;
    [ eauto with bdestruct
    | destruct H as [H | H];
       [ | try first [apply nlt_ge in H | apply nle_gt in H]]].

Tactic Notation "bdestruct" constr(X) := let H := fresh in bdestr X H.

Tactic Notation "bdestruct" constr(X) "as" ident(H) := bdestr X H.

Section ArrayMax.

(** Функция [array] ниже моделирует массив. [array i] есть [i]-й
элемент. Подразумевается, что индексы не превосходят некоторый
параметр [n]. Таким образом, [n] есть длина массива + 1. *)

Variable array : nat -> nat.

(** [arrayMax n] возвращает [max(array 0, ..., array n)]. Массив
непустой для любого n >= 0, поэтому максимум определен. *)

Fixpoint arrayMax (n : nat) : nat :=
match n with
| 0 => array 0
| S k => max (arrayMax k) (array n)
end.

(** Идентификаторы [Init.Nat.max] и т.п., появляющиеся в доказательстве,
обозначают то же, что и [max] *)

Theorem arrayMaxSpec1 :
  forall n i, i <= n -> array i <= arrayMax n.
Proof.
induction n as [| n IH]; intros i H.
* assert (H1 : i = 0) by lia. rewrite H1. reflexivity.
  (** Тактика [reflexivity] доказывает не только [M = M],
   но и [M <= M]. *)
* assert (H1 : i <= n \/ i = S n) by lia.
  clear H.
  (** Эта посылка больше не нужна. *)
  simpl.
  (** Упрощение [arrayMax (S n)] по определению. *)
  destruct H1 as [H1 | H1].
  + apply (le_trans _ (arrayMax n)).
    - auto.
      (** Следует непосредственно из предположения индукции. *)
    - apply le_max_l.
  + subst i.
    (** Или [rewrite H1]. *)
    apply le_max_r.
Qed.

(** Тактика [subst x] ищет посылку вида [x = M] или [M = x] и заменяет
[x] на [M] во всей цели. *)

(** Функция [arrayMax] вместо конструкции [if] использует [max], и
доказательство использует свойства [max] из библиотеки. Определим
аналогичную функцию с помощью [if] и используем рефлексию в
доказательстве. *)

Fixpoint arrayMax' (n : nat) : nat :=
match n with
| 0 => array 0
| S k => let p := arrayMax' k in
           if p <=? array n then array n else p
end.

Theorem arrayMaxSpec1' :
  forall n i, i <= n -> array i <= arrayMax' n.
Proof.
induction n as [| n IH]; intros i H.
* assert (H1 : i = 0) by lia. now rewrite H1.
* assert (H1 : i <= n \/ i = S n) by lia; clear H.
  simpl. destruct H1 as [H1 | H1].
  + apply (le_trans _ (arrayMax' n)).
    - auto.
    - bdestruct (arrayMax' n <=? array (S n)) as H.
      -- assumption.
      -- reflexivity.
  + subst i.
    bdestruct (arrayMax' n <=? array (S n)) as H.
    - easy.
    - now apply lt_le_incl.
Qed.

(** Докажем вторую часть спецификации, которая говорит, что
[arrayMax] берет результат из массива. *)

(** Нам понадобится лемма. *)

Lemma max_variants : forall m n, max m n = m \/ max m n = n.
Proof.
intros m n. destruct (max_spec m n) as [[_ H] | [_ H]]; [right | left]; assumption.
Qed.

Theorem arrayMaxSpec2 :
  forall n, exists i, i <= n /\ array i = arrayMax n.
Proof.
induction n as [| n IH].
* exists 0. split; reflexivity.
* destruct IH as [i [IH1 IH2]].
  simpl arrayMax. destruct (max_variants (arrayMax n) (array (S n))) as [H | H].
  + exists i. split; [auto |].
    congruence.
    (** Тактика [congruence] доказывает равенство из других равенств.
        Альтернативно: rewrite H; assumption. *)
  + exists (S n). rewrite H. split; reflexivity.
Qed.

(** Версия, использующая [arrayMax'] вместо [arrayMax]. *)

Theorem arrayMaxSpec2' :
  forall n, exists i, i <= n /\ array i = arrayMax' n.
Proof.
induction n as [| n IH].
* exists 0. split; reflexivity.
* destruct IH as [i [IH1 IH2]].
  simpl arrayMax'. bdestruct (arrayMax' n <=? array (S n)) as H.
  + exists (S n). split; auto.
  + exists i. split; auto.
Qed.

(** Еще одна реализация [arrayMax], на этот раз с хвостовой рекурсией. *)

Fixpoint arrayMaxHelp (n m : nat) : nat :=
match n with
| 0 => max (array 0) m
| S k => arrayMaxHelp k (max (array n) m)
end.

Definition arrayMaxTail (n : nat) : nat := arrayMaxHelp n (array n).

(** Докажем равенство [arrayMax] и [arrayMaxTail]. Сначала докажем
более общее утверждение про [arrayMax] и [arrayMaxHelp]. *)

Lemma maxHelpEqual : forall n m, max (arrayMax n) m = arrayMaxHelp n m.
Proof.
induction n as [| n IH]; intro m; [reflexivity |].
simpl. rewrite <- IH, max_assoc. reflexivity.
Qed.

Theorem maxEqual : forall n, arrayMax n = arrayMaxTail n.
Proof.
intro n; unfold arrayMaxTail. rewrite <- maxHelpEqual.
destruct n as [| n]; simpl.
* rewrite max_id; reflexivity.
* rewrite <- max_assoc, max_id; reflexivity.
Qed.

(** ** Зависимые суммы и квантор существования

Правило введения квантора существования в теории зависимых типов
выгладит примерно следующим образом.

[[
Γ |- M : A     Γ |- N : B[M/x]
------------------------------
   Γ |- (M, N) : (∃x : A, B)
]]

Как и в других правилах, если убрать термы [M], [N] и [(M, N)], то
полученное правило вывода является корректным в предикатной логике.

Таким образом, с точки зрения соответствия Карри-Говарда
доказательством утверждения [∃x : A, B] является пара термов [(M, N)].
Терм [M] является свидетелем существования, то есть объектом,
существование которого утверждается. Терм [N] является
доказательством, что [N] действительно удовлетворяет предикату [B], то
есть что [B[M/x]] имеет место.

Тип [∃x : A, B], элементами которого являются пары, называется
зависимой суммой (см. упражнение 3 в конце лекции 5). Это название,
как и в случае зависимого произведения, опирается на факт из теории
множеств. Суммой [B1 + B2], или дизъюнктным объединением, множеств
[B1] и [B2], называется объединении непересекающихся «копий» этих
множеств. Например, [B1 + B2] можно реализовать как [{(1, x) | x ∈ B1}
∪ {(2, y) | y ∈ B2}].

Это определение обобщается на произвольные семейства множеств
[{Bi | i ∈ A}]. Если [A = {1, 2, ...}], а [Bi] — множество для каждого
[i ∈ A], то элементами зависимой суммы [B1 + B2 + ...] являются пары
[(i, b)], где [i ∈ A] и [b ∈ Bi]. Это похоже на правило вывода
для квантора существования, приведенное выше. *)

(** ** Извлечение программ из конструктивных доказательств *)

(** С учетом того, что элементами зависимого произведения [forall x : A, B]
являются функции, которые [M : A] отображают в терм типа [B[M/x]] (см.
лекцию 5), термы типа [∀x : A, ∃y : B, P] — это функции, которые любой
терм [M : A] отображают в пару [(N, K)], где [N : B] и [K : P[M/x, N/y]].
Например,

[[
forall n, exists i, i <= n /\ array i = arrayMax n
]]

можно рассматривать как тип функций, которые принимает максимальный
индекс массива и возвращают индекс, где находится максимум.
Доказательство [arrayMaxSpec2] этого утверждения является программой,
вычисляющей эту функцию. Ее можно запустить в Coq и вычислить значение
на любом аргументе.

На самом деле в Coq есть две версии квантора существования:
[exists x : A, B] предназначен только для доказательств, а [{x : A | B}]
может использоваться для вычислений. Формулировка
[arrayMaxSpec2] использует первую версию, поэтому, чтобы иметь
возможность запускать доказательство как программу, нужно доказать
конструктивный аналог [arrayMaxSpec2]. *)

(** Это доказательство отличается от предыдущих лишь использованием
теоремы [max_dec], аналогичной лемме [max_variants]. *)

Theorem arrayMaxSpec2_constr :
  forall n, {i | i <= n /\ array i = arrayMax n}.
Proof.
induction n as [| n IH].
* exists 0. split; reflexivity.
* destruct IH as [i [IH1 IH2]].
  simpl arrayMax.
  destruct (max_dec (arrayMax n) (array (S n))) as [H | H];
    [exists i | exists (S n)]; (split; [auto | congruence]).
Defined.

(** Конструктивные теоремы должны заканчиваться с помощью [Defined],
а не [Qed]. *)

End ArrayMax.

(** *** Тестирование определенных выше функций *)

Check arrayMax.
Check arrayMaxSpec1.

Section ArrayTest.

(** Заведём переменную, про которую больше ничего не известно.
Она будет выполнять роль неопределенного значения. *)

Variable undef : nat.

Definition array (n : nat) : nat :=
match n with
| 0 => 4
| 1 => 2
| 2 => 7
| 3 => 2
| 4 => 0
| _ => undef
end.

(** mi означает "максимальный индекс". *)

Definition mi := 4. 

Compute arrayMax array mi.
Compute arrayMax' array mi.
Compute arrayMaxTail array mi.

(** Все три вычисления возвращают 7 — максимальный элемент в массиве.

Проверим работу [arrayMaxSpec2_constr] как функции, которая возвращает
индекс, где находится максимум. Библиотечная функция [proj1_sig p] возвращает
первую компоненту пары [p] типа [{i : nat | ...}]. *)

Compute proj1_sig (arrayMaxSpec2_constr array mi).

(** Возвращает [2], так как [array 2 = 7].

В случае функции [arrayMax] мы сначала написали функцию, а потом
доказали, что она соответствует своей спецификации. Использование
конструктивных доказательств, таких как [arrayMaxSpec2_constr], в
качестве программ согласно соответствию Карри-Говарда является еще
одним способом получить верифицированную программу. Такая программа
является правильной по построению. Таким образом, вместо написания
программы можно составить конструктивное доказательство существования
необходимого объекта. При этом программирование и доказательство
теорем сливаются в одно. В некотором точном смысле конструктивное
доказательство — это программа, которая переделывает свидетельство
того, что дано, в свидетельство того, что нужно доказать.

Нормализация в Coq терма-доказательства утверждения о существовании
какого-то объекта является не очень эффективным способом построения
этого объекта, потому что значительная часть терма посвящена
доказательству того, что объект обладает нужным свойством. Это
доказательство затем отбрасывается. Coq умеет преобразовывать
доказательства в программы на языках функционального программирования
OCaml, Haskell и Scheme. При этом неконструктивные части
доказательства удаляются. *)

End ArrayTest.

(** Извлечем программу на Scheme из доказательства [arrayMaxSpec2_constr]. *)

Require Extraction.

Extraction Language Scheme.

Extraction arrayMaxSpec2_constr.

(** Извлеченный код.

[[
(define arrayMaxSpec2_constr (lambdas (array n)
  (match n
     ((O) `(O))
     ((S n0)
       (let ((s (@ max_dec0 (@ arrayMax array n0)
                            (array `(S ,n0)))))
         (match s
            ((Left) (@ arrayMaxSpec2_constr array n0))
            ((Right) `(S ,n0))))))))
]]
*)
