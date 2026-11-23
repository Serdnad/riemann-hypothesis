module

public import Formalism.LocalToGlobal.HermitianForms.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.CmpGlMemMIff
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOneRec
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.AlgebraMapUnitZpow
public import Formalism.SharpRestriction.GrowthBounds.LatticeMultiplicityLemmas.LatticeMultiplicityCheck.Retype
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.HermitianColumns.Bundle002
public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Formalism.LocalToGlobal.HermitianForms.Bundle010

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure LocPart (D : D7) {p : ℕ} (G : GAtP p) (Ch : Type) (n : ℕ) where
  cmpt : Ch → Type
  [fin : ∀ β, Fintype (cmpt β)]
  eC : (Σ β, cmpt β) ≃ G.comp
  loc : ∀ β, LocAt D.host.F D.host.E n (gatCh G fun a : cmpt β => eC ⟨β, a⟩)
  pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ D.what₂.Tau

attribute [instance] LocPart.fin

variable {D : D7} {Tw : TwForms D} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)}


theorem badQ_notOver (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hQ : okQ D Q w) (w' : HeightOneSpectrum (𝓞 D.host.F)) (hw : w' ∈ badQ D Q) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal := by
  rcases hw with h | h
  · exact bad_notOver u w hg w' h
  · exact hQ w' h

end Formalism.MainNotions.G.CmpJ

end
end

section

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.L2.G.Cmp

section Final

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure KerLabelsMu where
  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m
  cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j
  cls_iff : ∀ j, j ≤ D.R.m → ∀ (a a' : Lv.comp j) (L L' : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    (Fl.Pj j).IsLatTup L' →
    (cls j a L = cls j a' L' ↔ a = a' ∧ ∃ γ : (Lv.lev j a).Γ, L' = (Lv.lev j a).smul γ L)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u μ).cls j, ∃ a L, (Fl.Pj j).IsLatTup L ∧ cls j a L = x
  stab_zero : ∀ (a : Lv.comp 0) (L : (Fl.Pj 0).Tup), (Fl.Pj 0).IsLatTup L →
    Nat.card {γ : (Lv.lev 0 a).Γ // (Lv.lev 0 a).smul γ L = L} = 1
  stab_dvd : ∀ j, j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    0 < Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L} ∧
      Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L} ∣ (D.mem u).C.DGam
  rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j

  stab_eq : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    Nat.card ((D.chTw u μ).stab j (cls j a L)) = Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L}

variable {c Tw u μ w h Lv}

def kerAtMu_of (K : KerLabelsMu Tw u μ w h Lv) (X : StepsMu c Tw u μ w h Lv) (hd : DescUp c u w h Lv)
    (hs : ValScalar c u w h) (hf : LocFree Tw u μ w D.R.m) : TwTie.KerAtMu D c Tw u μ w h (chainMu X.up) where
  fl_t := K.fl_t
  fl_m := K.fl_m
  cls := K.cls
  cls_iff := K.cls_iff
  cls_surj := K.cls_surj
  stab_zero := K.stab_zero
  stab_dvd := K.stab_dvd
  cmp := X.up.cmp
  cmp_inj := X.up.inj
  cmp_zero := X.up.cmp_zero
  cmp_int := X.cmp_int hd
  cmp_K := chainMu_cmp_K X.up
  rat := K.rat
  val := X.up.val_of D.R.m le_rfl (X.cmp_int hd D.R.m le_rfl) hs hf

end Final

section Rec

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

def kerAtMu (K : KerLabelsMu Tw u μ w h Lv) (X : StepsMu c Tw u μ w h Lv) (hd : DescUp c u w h Lv)
    (v : Fin (D.gat u w h).P.nV) : TwTie.KerAtMu D c Tw u μ w h (chainMu X.up) :=
  kerAtMu_of K X hd (valScalar_of_place c u w h v) (locFree Tw u μ w D.R.m)

end Rec

end Formalism.MainNotions.G.CmpJ

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m) {cmp : Type} [Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}
  (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
  (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E)

theorem locJ_iw_F (v : Fin (gatCh (gatJ Lv (i + 1)) em).P.nV) (a : D.host.F) :
    (locJ hi t B).iw v (algebraMap D.host.F D.host.E a) =
      ((locJ hi t B).eQ v).symm (algebraMap D.host.F (((locJ hi t B).pl v).1.adicCompletion D.host.F) a) :=
  congrArg ((locJ hi t B).eQ v).symm ((X.g u w hg).spl_F _ ((X.g u w hg).pl v).2 a)

theorem locJ_pos_emb {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D} (K : CmpTied D X T Gt c)
    (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E) :
    c.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (Fl.Pj (i + 1)).ι v (((Fl.Pj (i + 1)).σ v ^ s.val) ((locJ hi t B).iw v x)) :=
  (K.tie u w hg).pos_emb v s x

end Formalism.MainNotions.G.CmpJ

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {Tau : Type} [Fintype Tau] {n : ℕ}

theorem val_tw_iff (hn : 0 < n) (k a : ℂ) (hk : k ≠ 0) (ha : a ≠ 0) (G : Tau → Matrix (Fin n) (Fin n) ℂ) (lam : Tau → DomWeight n) (c : ℤ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (Q : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z : Formalism.L2.Forms.Frames G) (v : ℂ) :
    v = fnOf G (shiftOf (fun τ => shW (lam τ) c)) M Q z ↔
      k * (a * detF c z * v) = fnOf G (shiftOf lam) M ((k * a * ∏ τ, (M τ).det ^ (-c)) • Q) z := by
  have h1 : fnOf G (shiftOf lam) M ((k * a * ∏ τ, (M τ).det ^ (-c)) • Q) z =
      k * (a * ((∏ τ, (M τ).det ^ (-c)) * fnOf G (shiftOf lam) M Q z)) := by
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1]
  constructor
  · intro hv
    rw [nrm_val_M hn a G lam c M hM Q z v hv]
  · intro hv
    exact nrm_val_M' hn a ha G lam c M hM Q z v (mul_left_cancel₀ hk hv)

end Gen

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p} (S : StepIn M i hi G)

namespace StepIn

def sTw (β : S.Ch) (cl : {c // S.chOf c = β}) (B' : GL (Fin (D.R.N i)) D.host.E) : ℂ :=
  S.kTw β * ((S.tw β).ch ((S.K β).y cl) : ℂ) *
    ∏ τ, (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ).det ^ (-(cTw D i))

def TwUnit (w : D.what₂.places.Pl) (β : S.Ch) : Prop :=
  ∀ (cl : {c // S.chOf c = β}) (B' : GL (Fin (D.R.N i)) D.host.E),
    IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (S.lat cl.1)) B' →
    ∃ r : D.what₂.LL, r ∈ Formalism.BasicNotions.intW D.what₂.places w ∧ r⁻¹ ∈ Formalism.BasicNotions.intW D.what₂.places w ∧ D.what₂.embLL r = S.sTw β cl B'

def IntAtN (w : D.what₂.places.Pl) (β : S.Ch) (x : (M.lat i).V) (cl : {c // S.chOf c = β}) : Prop :=
  ∀ B' : GL (Fin (D.R.N i)) D.host.E,
    IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (S.lat cl.1)) B' →
    ∃ Pp ∈ IntSpan D w (M.lam i), ∀ z : Fr D i hi, S.embN β x cl z =
      fnOf _ (shiftOf (M.lam i)) (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Pp z

variable {S}

theorem sTw_ne (β : S.Ch) (cl : {c // S.chOf c = β}) (B' : GL (Fin (D.R.N i)) D.host.E) : S.sTw β cl B' ≠ 0 :=
  mul_ne_zero (mul_ne_zero (S.kTw_ne β) (Units.ne_zero _))
    (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (atInf_det_unit (embT D) B'⁻¹ τ).ne_zero)



theorem intAtJ_iff_N (w : D.what₂.places.Pl) (β : S.Ch) (hU : S.TwUnit w β) (x : (M.lat i).V) (cl : {c // S.chOf c = β}) :
    S.IntAtJ w β x cl ↔ S.IntAtN w β x cl := by
  refine forall_congr' fun B' => forall_congr' fun hB => ?_
  obtain ⟨r, hr, hr', er⟩ := hU cl B' hB
  have key : ∀ (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) (z : Fr D i hi),
      M.emb i x cl.1 (S.eY.symm z) =
        fnOf _ (shiftOf (lamTG M i)) (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q z ↔
      S.embN β x cl z = fnOf _ (shiftOf (M.lam i)) (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1)
        (D.what₂.embLL r • Q) z := by
    intro Q z
    rw [er]
    exact val_tw_iff (D.R.N_pos i) (S.kTw β) _ (S.kTw_ne β) (Units.ne_zero _) _ (M.lam i) (cTw D i) _
      (atInf_det_unit (embT D) B'⁻¹) Q z _
  have hr0 : D.what₂.embLL r ≠ 0 := by rw [er]; exact sTw_ne β cl B'
  constructor
  · rintro ⟨Q, hQ, h⟩
    refine ⟨D.what₂.embLL r • Q, intSpan_smul w (M.lam i) r hr hQ, fun z => (key Q z).1 ?_⟩
    rw [h, Equiv.apply_symm_apply]
  · rintro ⟨Q, hQ, h⟩
    refine ⟨D.what₂.embLL r⁻¹ • Q, intSpan_smul w (M.lam i) r⁻¹ hr' hQ, fun z' => ?_⟩
    have h1 := (key (D.what₂.embLL r⁻¹ • Q) (S.eY z')).2 (by
      rw [smul_smul, map_inv₀, mul_inv_cancel₀ hr0, one_smul]
      exact h _)
    rwa [Equiv.symm_apply_apply] at h1

variable (S)

def ValIntN (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl) : Prop :=
  ∀ β, ValIntAt (S.K β).lev (embT D) D.what₂.embLL (S.charts.gat β) e (S.loc β) S.pos (S.embN β) (S.K β).y (S.IntAtN w β)

variable {S}

theorem valIntJ_of (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl) (hU : ∀ β, S.TwUnit w β) (h : S.ValIntN e w) : S.ValIntJ e w :=
  fun β x a L cl hL hp => (h β x a L cl hL hp).trans (intAtJ_iff_N w β (hU β) x cl).symm

end StepIn

end Formalism.MainNotions.G.CmpJ

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G.Cmp

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def FillTie (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w hg)) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (b : ℕ) (hb : b < D.R.m),
    ((Fl.w v (b + 1) s : ℤ) : ℚ) = wG D.R ((D.hcW u (Gt.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩) (b + 1)

theorem rk_of (Gt : GatTies D) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (j : ℕ) : (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1) := by
  have hk := Gt.gat_k u w hg
  show (D.gat u w hg).P.m + (j + 1) * (Fl.t + 1) + 1 = D.R.k + (j + 1) * (D.R.t + 1)
  rw [ht]
  omega

theorem wtTie_of (Gt : GatTies D) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w hg Fl) (j : ℕ) (hj : j + 1 ≤ D.R.m)
    (rk : (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1)) :
    WtTie (Fl.Pj (j + 1)) rk (Gt.gat_pos u w hg) (M.lam (j + 1)) := by
  intro (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) i
  have hk := Gt.gat_k u w hg
  show liftWt Fl.t (D.gat u w hg).P.m ((D.gat u w hg).P.lam0 v s) (fun a => Fl.w v a s) (j + 1) i =
    (M.lam (j + 1) (Gt.gat_pos u w hg ⟨v, s⟩)).w (finCongr rk i)
  apply Int.cast_injective (α := ℚ)
  rw [M.lam_eq (j + 1) hj (Gt.gat_pos u w hg ⟨v, s⟩) (finCongr rk i)]
  have hi : ((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) = i.val := rfl
  unfold liftWt
  by_cases h1 : i.val < (D.gat u w hg).P.m + 1
  · have h2 : ((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) < D.R.k := by rw [hi, ← hk]; exact h1
    rw [dif_pos h1, dif_pos h2, Gt.gat_lam u w hg v s ⟨i.val, h1⟩, (D.fm u).lam_eq 0 (Nat.zero_le _) _ _]
    exact dif_pos h2
  · have h2 : ¬ ((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) < D.R.k := by rw [hi, ← hk]; exact h1
    rw [dite_eq_right h1, dite_eq_right h2, Int.cast_neg]
    congr 1
    have e1 : (i.val - ((D.gat u w hg).P.m + 1)) / (Fl.t + 1) =
        (((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) - D.R.k) / (D.R.t + 1) := by rw [hk, ht, hi]
    rw [e1]
    exact hF v s _ (D.R.blk_lt hj (finCongr rk i) h2)


variable {M} in
theorem StepIn.wt_of (Gt : GatTies D) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Fl : Fills (D.gat u w hg)} (Lv : Levels Fl) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w hg Fl) (j : ℕ) (hj : j + 1 ≤ D.R.m)
    (S : StepIn M (j + 1) hj (gatJ Lv (j + 1))) (hpos : S.pos = Gt.gat_pos u w hg) (β : S.Ch) :
    WtTie (gatJ Lv (j + 1)).P (S.loc β).rk S.pos (M.lam (j + 1)) := by
  rw [hpos]
  exact wtTie_of M Gt w hg Fl ht hF j hj _

end Formalism.MainNotions.G.CmpJ

end
end
