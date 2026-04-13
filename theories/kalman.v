(*  Формальная верификация дискретного фильтра Калмана                *)

From HB Require Import structures.
From mathcomp.boot Require Import all_boot.
From mathcomp.algebra Require Import ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import order.
From mathcomp.classical Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.
Import Order.Theory.
Open Scope ring_scope.

Lemma trmx_add (K : realFieldType) m n (A C : 'M[K]_(m, n)) : (A + C)^T = A^T + C^T.
Proof.
  apply/matrixP => i j.
  by rewrite !mxE.
Qed.

(* ================================================================== *)
(* §0  Предикат положительной полуопределённости (ключевой для        *)
(*     ковариационных матриц)                                         *)
(* ================================================================== *)

Section PSD.
Variable (R : realFieldType).

Definition psd n (M : 'M[R]_n) : Prop :=
  M = M^T /\ forall (v : 'cV[R]_n), \tr (v^T *m M *m v) >= 0.

Definition pd n (M : 'M[R]_n) : Prop :=
  M = M^T /\ forall (v : 'cV[R]_n), v != 0 -> \tr (v^T *m M *m v) > 0.

Lemma pd_psd n (M : 'M[R]_n) : pd M -> psd M.
Proof.
case=> Msym pdM; split=> // v.
have [v0|vNZ] := boolP (v == 0); last first.
  have /andP[_ le0tr]:
      (\tr (v^T *m M *m v) != 0) && (0 <= \tr (v^T *m M *m v)).
    by rewrite -lt0r; exact: (pdM v vNZ).
  exact: le0tr.
move/eqP: v0=> v0; subst v.
by rewrite trmx0 mul0mx mulmx0 mxtrace0 lexx.
Qed.

Lemma psd_add n (A B : 'M[R]_n) : psd A -> psd B -> psd (A + B).
Proof.
move=> [Asym psdA] [Bsym psdB]; split.
  apply/matrixP=> i j.
  have hA' : (A j i) = ((A^T) j i).
  case Asym.
  done.
  have hA0 : ((A^T) j i) = A i j.
  by rewrite mxE.
  have hA : (A j i) = (A i j) := eq_trans hA' hA0.
  have hB' : (B j i) = ((B^T) j i).
  case Bsym.
  done.
  have hB0 : ((B^T) j i) = B i j.
  by rewrite mxE.
  have hB : (B j i) = (B i j) := eq_trans hB' hB0.
  rewrite !mxE hA hB.
  done.
move=> v; rewrite mulmxDr mulmxDl mxtraceD.
exact: (addr_ge0 (psdA v) (psdB v)).
Qed.

Lemma psd_congruence n p (A : 'M[R]_n) (M : 'M[R]_(n, p)) :
  psd A -> psd (M^T *m A *m M).
Proof.
  case=> Asym psdA; split.
    by rewrite trmx_mul trmx_mul !trmxK mulmxA -Asym.
    by move=> v; rewrite !mulmxA -mulmxA -trmx_mul; exact: psdA (M *m v).
Qed.

Lemma psd_mulmx_row n m (A : 'M[R]_m) (M : 'M[R]_(n, m)) :
  psd A -> psd (M *m A *m M^T).
Proof.
  move=> psdA; have -> : (M *m A *m M^T) = (M^T)^T *m A *m M^T by rewrite trmxK.
  exact: (@psd_congruence _ _ A M^T psdA).
Qed.

Lemma psd_tr_ge0 n (M : 'M[R]_n) : psd M -> \tr M >= 0.
Proof.
  case=> Msym psdM; rewrite -(@mxtrace0 _ n) /mxtrace; apply: ler_sum => i _.
  rewrite mxE; have h := psdM (delta_mx i ord0).
  by rewrite trmx_delta -rowE -colE trace_mx11 !mxE in h.
Qed.

Lemma pd_invertible n (M : 'M[R]_n) : pd M -> M \in unitmx.
Proof.
  move=> [Msym pdM]; apply: contraT => Mnu.
  have Cnz : cokermx M != 0 by rewrite cokermx_eq0 row_full_unit.
  have /matrix0Pn [i [j Cij_nz]] := Cnz.
  pose v := cokermx M *m delta_mx j ord0 : 'cV[R]_n.
  have vNZ : v != 0.
  apply/cV0Pn; exists i; rewrite /v -colE mxE; exact: Cij_nz.
  have Mv0 : M *m v = 0 by rewrite /v mulmxA mulmx_coker mul0mx.
  by move: (pdM v vNZ); rewrite -mulmxA Mv0 mulmx0 mxtrace0 ltxx.
Qed.

End PSD.

(* ================================================================== *)
(* §1  Модель пространства состояний и шаг предсказания               *)
(* ================================================================== *)

Section KalmanFilter.
Variable (R : realFieldType).
Variables (n m p : nat).

Variable F : 'M[R]_n.             (* матрица перехода состояний *)
Variable B : 'M[R]_(n, p).        (* матрица управляющего воздействия *)
Variable H : 'M[R]_(m, n).        (* матрица наблюдения *)
Variable Q : 'M[R]_n.             (* ковариация шума процесса *)
Variable Rcov : 'M[R]_m.          (* ковариация шума измерения *)

(* Общие предположения о ковариациях шума *)
Hypothesis Q_psd  : psd Q.
Hypothesis R_pd   : pd Rcov.

(* Шаг предсказания *)

Definition predict_state (x_prev : 'cV[R]_n) (u : 'cV[R]_p) : 'cV[R]_n :=
  F *m x_prev + B *m u.

Definition predict_cov (P_prev : 'M[R]_n) : 'M[R]_n :=
  F *m P_prev *m F^T + Q.

(* Предсказанная ковариация симметрична *)
Lemma predict_cov_sym (P : 'M[R]_n) :
  P = P^T -> predict_cov P = (predict_cov P)^T.
Proof.
  move=> Psym.
  have hP : (F *m P *m F^T)^T = F *m P *m F^T.
    by rewrite trmx_mul trmx_mul !trmxK -mulmxA -Psym.
  rewrite /predict_cov trmx_add hP -Q_psd.1.
  done.
Qed.

(* Предсказанная ковариация сохраняет положительную полуопределённость *)
Lemma predict_cov_psd (P : 'M[R]_n) :
  psd P -> psd (predict_cov P).
Proof.
move=> pPs.
have h1 : psd (F *m P *m F^T) := psd_mulmx_row n n P F pPs.
have h2 : psd Q := Q_psd.
have hsum : psd (F *m P *m F^T + Q) := psd_add h1 h2.
exact: (by simpa [predict_cov] using hsum).
Qed.

(* ================================================================== *)
(* §2  Инновационная ковариация, усиление Калмана,                    *)
(*     обновление ковариации                                          *)
(* ================================================================== *)

(* Инновационная ковариация *)

Definition innov_cov (P_pred : 'M[R]_n) : 'M[R]_m :=
  H *m P_pred *m H^T + Rcov.

Lemma innov_cov_pd (P_pred : 'M[R]_n) :
  psd P_pred -> pd (innov_cov P_pred).
Proof. Admitted.

Lemma innov_cov_inv (P_pred : 'M[R]_n) :
  psd P_pred -> innov_cov P_pred \in unitmx.
Proof. Admitted.

(* Усиление (коэффициент) Калмана *)

Definition kalman_gain (P_pred : 'M[R]_n) : 'M[R]_(n, m) :=
  P_pred *m H^T *m invmx (innov_cov P_pred).

(* Обновление состояния *)

Definition update_state (P_pred : 'M[R]_n)
    (x_pred : 'cV[R]_n) (z : 'cV[R]_m) : 'cV[R]_n :=
  let K := kalman_gain P_pred in
  x_pred + K *m (z - H *m x_pred).

(* Обновление ковариации (стандартная форма) *)

Definition update_cov (P_pred : 'M[R]_n) : 'M[R]_n :=
  let K := kalman_gain P_pred in
  (1%:M - K *m H) *m P_pred.

(* Форма Джозефа (алгебраически эквивалентна, удобна для доказательств) *)

Definition joseph_form (P_pred : 'M[R]_n) : 'M[R]_n :=
  let K := kalman_gain P_pred in
  let ImKH := 1%:M - K *m H in
  ImKH *m P_pred *m ImKH^T + K *m Rcov *m K^T.

(* Форма Джозефа совпадает со стандартным обновлением при усилении Калмана *)
Lemma joseph_eq_update (P_pred : 'M[R]_n) :
  psd P_pred ->
  joseph_form P_pred = update_cov P_pred.
Proof. Admitted.

(* Сохранение PSD через обновление (центральный результат) *)

Lemma update_cov_psd (P_pred : 'M[R]_n) :
  psd P_pred -> psd (joseph_form P_pred).
Proof.
  (* Набросок: joseph_form = (I-KH) P (I-KH)^T + K R K^T.
     Первое слагаемое PSD по psd_congruence; второе PSD по
     psd_congruence на R; сумма PSD по psd_add. *)
Admitted.

(* Симметричность обновлённой ковариации *)
Lemma update_cov_sym (P_pred : 'M[R]_n) :
  psd P_pred -> joseph_form P_pred = (joseph_form P_pred)^T.
Proof. Admitted.

(* Монотонность ковариации: след не возрастает *)

Lemma update_cov_trace_le (P_pred : 'M[R]_n) :
  psd P_pred ->
  \tr (update_cov P_pred) <= \tr P_pred.
Proof. Admitted.

(* ================================================================== *)
(* §3  Несмещённость                                                  *)
(* ================================================================== *)

(* Абстрактный оператор математического ожидания (алгебраическая
   аксиоматизация). Моделируем E как матричнозначное линейное
   отображение, избегая использования сложной теории меры. *)

Variable Exp : forall {r c : nat}, 'M[R]_(r, c) -> 'M[R]_(r, c).

(* Аксиомы линейности *)
Hypothesis Exp_add : forall r c (A B : 'M[R]_(r, c)),
  Exp (A + B) = Exp A + Exp B.
Hypothesis Exp_scale : forall r c (a : R) (A : 'M[R]_(r, c)),
  Exp (a *: A) = a *: Exp A.
Hypothesis Exp_mulmx_l : forall r c s (A : 'M[R]_(r, c)) (B : 'M[R]_(c, s)),
  Exp (A *m B) = A *m Exp B.

(* Предположения о шумах *)
Variable w : nat -> 'cV[R]_n.
Variable v : nat -> 'cV[R]_m.
Hypothesis Exp_w_zero : forall k, Exp (w k) = 0.
Hypothesis Exp_v_zero : forall k, Exp (v k) = 0.

(* Обновление истинного вектора состояния *)
Definition x_true (u : nat -> 'cV[R]_p) : nat -> 'cV[R]_n :=
  fix f k :=
    match k with
    | 0%N => w 0%N
    | k'.+1 => F *m f k' + B *m u k' + w k'.+1
    end.

(* Обновление оценочного вектора состояния *)
Definition x_hat (u : nat -> 'cV[R]_p) (z : nat -> 'cV[R]_m)
    (P_seq : nat -> 'M[R]_n) : nat -> 'cV[R]_n :=
  fix f k :=
    match k with
    | 0%N => 0  (* начальная оценка; предполагаем несмещённый старт *)
    | k'.+1 =>
      let x_pred := predict_state (f k') (u k') in
      let P_pred := predict_cov (P_seq k') in
      update_state P_pred x_pred (z k'.+1)
    end.

(* Ошибка оценивания *)
Definition err u z Ps k := x_true u k - x_hat u z Ps k.

(* Несмещённость: E[ошибка] = 0 на каждом шаге *)
Theorem unbiased u z Ps :
  Exp (err u z Ps 0) = 0 ->
  forall k, Exp (err u z Ps k) = 0.
Proof.
  (* Набросок: индукция по k. Ошибка на шаге k+1 раскладывается через
     уравнения состояния и обновления в линейную комбинацию ошибки на
     шаге k (ноль по предположению индукции) и шумов w, v (ноль по гипотезе). *)
Admitted.

(* ================================================================== *)
(* §4  Оптимальность усиления Калмана                                 *)
(* ================================================================== *)

(* Для любого альтернативного усиления K' след апостериорной ковариации
   не меньше, чем при усилении Калмана. *)

Definition alt_update_cov (K' : 'M[R]_(n, m)) (P_pred : 'M[R]_n) : 'M[R]_n :=
  let ImKH := 1%:M - K' *m H in
  ImKH *m P_pred *m ImKH^T + K' *m Rcov *m K'^T.

Theorem kalman_gain_optimal (P_pred : 'M[R]_n) (K' : 'M[R]_(n, m)) :
  psd P_pred ->
  \tr (update_cov P_pred) <= \tr (alt_update_cov K' P_pred).
Proof.
  (* Набросок: раскрыть alt_update_cov с K' = K + dK, выделить полный
     квадрат; перекрёстные члены обнуляются для усиления Калмана,
     остаётся PSD-остаток с неотрицательным следом. *)
Admitted.

(* Характеристика через производную: dTr(P+)/dK = 0 при усилении Калмана *)
Theorem gain_stationary_point (P_pred : 'M[R]_n) :
  psd P_pred ->
  kalman_gain P_pred *m innov_cov P_pred = P_pred *m H^T.
Proof. Admitted.

(* ================================================================== *)
(* §5  Наблюдаемость и управляемость                                  *)
(* ================================================================== *)

(* Наблюдаемость: пара (H, F) наблюдаема, когда составная матрица
   [H; HF; HF^2; ...; HF^{n-1}] имеет полный столбцовый ранг.
   Вместо явного построения блочной матрицы формулируем условие
   на ранг через ядро отображения. *)

Definition obsv_block (i : nat) : 'M[R]_(m, n) :=
  H *m (F ^+ i).

Definition observable : Prop :=
  forall (x : 'cV[R]_n), (forall i : 'I_n, obsv_block i *m x = 0) -> x = 0.

(* Управляемость: пара (F, B) управляема, когда составная матрица
   [B, FB, F^2 B, ..., F^{n-1} B] имеет полный строковый ранг. *)

Definition ctrl_block (i : nat) : 'M[R]_(n, p) :=
  (F ^+ i) *m B.

Definition controllable : Prop :=
  forall (y : 'rV[R]_n), (forall i : 'I_n, y *m ctrl_block i = 0) -> y = 0.

(* Полная наблюдаемость ⇒ ковариация ошибки может уменьшаться *)
Lemma observable_cov_decrease :
  observable ->
  forall (P0 : 'M[R]_n), psd P0 ->
  exists k : nat, \tr (iter k (fun P => update_cov (predict_cov P)) P0) <=
                  \tr P0.
Proof. Admitted.

(* Ненаблюдаемые моды не поддаются оцениванию *)
Lemma unobservable_mode :
  ~ observable ->
  exists (x0 : 'cV[R]_n), x0 != 0 /\
    forall (i : 'I_n), obsv_block i *m x0 = 0.
Proof. Admitted.

(* ================================================================== *)
(* §6  Сходимость / неподвижная точка Риккати                         *)
(* ================================================================== *)

(* Дискретное алгебраическое уравнение Риккати (DARE) *)
Definition riccati_step (P : 'M[R]_n) : 'M[R]_n :=
  update_cov (predict_cov P).

Definition is_riccati_fixpoint (Pss : 'M[R]_n) : Prop :=
  Pss = riccati_step Pss.

(* Существование PSD-неподвижной точки при стандартных условиях *)
Theorem riccati_fixpoint_exists :
  observable -> controllable ->
  exists Pss : 'M[R]_n, is_riccati_fixpoint Pss /\ psd Pss.
Proof. Admitted.

(* Сходимость итерации Риккати *)
Theorem riccati_convergence (P0 : 'M[R]_n) :
  observable -> controllable -> psd P0 ->
  exists Pss : 'M[R]_n,
    is_riccati_fixpoint Pss /\ psd Pss /\
    forall eps : R, eps > 0 ->
      exists N : nat, forall k, (N <= k)%N ->
        \tr (iter k riccati_step P0 - Pss) < eps.
Proof.
  (* Набросок: при наблюдаемости + управляемости спектральный радиус
     замкнутого отображения (I - K_ss H) F < 1; аргумент Ляпунова
     показывает, что P_k сжимается к Pss. Полное доказательство
     требует теории собственных значений. *)
Admitted.

(* Единственность стабилизирующей PSD-неподвижной точки *)
Theorem riccati_fixpoint_unique :
  observable -> controllable ->
  forall P1 P2 : 'M[R]_n,
    is_riccati_fixpoint P1 -> psd P1 ->
    is_riccati_fixpoint P2 -> psd P2 ->
    P1 = P2.
Proof. Admitted.

(* ================================================================== *)
(* §7  Один шаг фильтра (удобная обёртка)                             *)
(* ================================================================== *)

Record kf_state := KFState {
  kf_x : 'cV[R]_n;
  kf_P : 'M[R]_n;
}.

Definition kf_predict (st : kf_state) (u : 'cV[R]_p) : kf_state :=
  KFState (predict_state (kf_x st) u) (predict_cov (kf_P st)).

Definition kf_update (st : kf_state) (z : 'cV[R]_m) : kf_state :=
  let P_pred := kf_P st in
  KFState (update_state P_pred (kf_x st) z) (update_cov P_pred).

Definition kf_step (st : kf_state) (u : 'cV[R]_p) (z : 'cV[R]_m) :
    kf_state :=
  kf_update (kf_predict st u) z.

(* Инвариант PSD через полный цикл предсказание–обновление *)
Lemma kf_step_psd (st : kf_state) (u : 'cV[R]_p) (z : 'cV[R]_m) :
  psd (kf_P st) -> psd (kf_P (kf_step st u z)).
Proof.
  (* Композиция predict_cov_psd и update_cov_psd *)
Admitted.

End KalmanFilter.
