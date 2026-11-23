module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.Columns.Bundle038
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
public import Formalism.LocalToGlobal.Columns.Bundle014
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle382
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle362
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle482
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle376
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle360
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle115
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle486
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.Bl

theorem resCharW_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) :
    Examples₂.PlacesToy.resCharW (Formalism.DivisionValues.conjPl w) = Examples₂.PlacesToy.resCharW w := by
  have hm : ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal := by
    have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO K) (Examples₂.PlacesToy.resCharW_mem w)
    rwa [map_natCast] at this
  exact Examples₂.PlacesToy.prime_mem_unique _ (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) hm

theorem FTypeG_of_kapDef {D : D7} (hk : DV.KapDef D) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    FTypeG D j = -(∑ τ : D.what₂.Tau, ((∑ i : Fin (D.R.sigW j).1, |((DV.aPlusQ D j τ i : ℚ) : ℝ)|) +
      ∑ c : Fin (D.R.sigW j).2, |((DV.aMinusQ D j τ c : ℚ) : ℝ)|)) / 2 := by
  unfold FTypeG fockDeg
  congr 2
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨hb, hs⟩ := hk j h1 h2 τ
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hb i]
    norm_cast
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [show ((DV.aMinusQ D j τ c : ℚ) : ℝ) = -((D.what₂.kaSmall j τ c : ℚ) : ℝ) by rw [hs c]; push_cast; ring, abs_neg]
    norm_cast

theorem mem_W1F_forced_iff (s : Scale) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt)
    (v : HeightOneSpectrum (𝓞 B.LL)) :
    v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K s (w.D Z)) ↔
      ∃ j : ℕ, j < B.R.m ∧ FK s (w.D Z) (j + 1) (Examples₂.PlacesToy.resCharW v) ≠ 0 := by
  constructor
  · rintro ⟨j, y, hy, h⟩
    refine ⟨j.1, j.2, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact h
    · have e : F0K s (w.D Z) (Formalism.DivisionValues.conjPl v) j = FK s (w.D Z) (j.1 + 1) (Examples₂.PlacesToy.resCharW v) := by
        show FK s (w.D Z) (j.1 + 1) (Examples₂.PlacesToy.resCharW (Formalism.DivisionValues.conjPl v)) = _
        rw [resCharW_conjPl]
      exact e ▸ h
  · rintro ⟨j, hj, h⟩
    exact ⟨⟨j, hj⟩, v, Or.inl rfl, h⟩

theorem FK_enl (s : Scale) {B B' : Base} {f : Fr B.toPre} {T : TwDat B} {f' : Fr B'.toPre} {T' : TwDat B'}
    (w : ColW B f T) (w' : ColW B' f' T') (Z : w.Lt) (Z' : w'.Lt) (h : B'.toPre = B.toPre)
    (hk : DV.KapDef (w.D Z)) (hk' : DV.KapDef (w'.D Z')) (j p : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ B.R.m) :
    FK s (w.D Z) j p = FK s (w'.D Z') j p := by
  have h2' : j ≤ B'.R.m := by rw [h]; exact h2
  unfold FK
  rw [FTypeG_of_kapDef hk h1 h2, FTypeG_of_kapDef hk' h1 h2']
  clear hk hk'
  cases B'
  subst h
  rfl

theorem resCharW_of_below {B B' : Base} {f : Fr B.toPre} {T : TwDat B} {f' : Fr B'.toPre} {T' : TwDat B'}
    (w : ColW B f T) (w' : ColW B' f' T') (Z : w.Lt) (Z' : w'.Lt) (v : HeightOneSpectrum (𝓞 B.LL))
    (v' : HeightOneSpectrum (𝓞 B'.LL)) (hB : Below (w.D Z) (w'.D Z') v v') :
    Examples₂.PlacesToy.resCharW v' = Examples₂.PlacesToy.resCharW v := by
  have he : (w.D Z).what₂.embLL (((Examples₂.PlacesToy.resCharW v : ℕ) : 𝓞 (w.D Z).what₂.LL) : (w.D Z).what₂.LL) =
      (w'.D Z').what₂.embLL (((Examples₂.PlacesToy.resCharW v : ℕ) : 𝓞 (w'.D Z').what₂.LL) : (w'.D Z').what₂.LL) := by
    simp only [map_natCast]
  have hm := (hB _ _ he).1 (Examples₂.PlacesToy.resCharW_mem v)
  exact Examples₂.PlacesToy.prime_mem_unique _ (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) hm

theorem nonzeroForcedContentPlaces_agree_over_enlargement : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B')
    (w' : ColW B' f' T'), Enl B B' → ∀ (Z : w.Lt) (Z' : w'.Lt), DV.KapDef (w.D Z) → DV.KapDef (w'.D Z') →
    ∀ v v', Below (w.D Z) (w'.D Z') v v' →
      (v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K K.s (w.D Z)) ↔ v' ∈ R3.placesWithNonzeroContentOrConj (w'.D Z') (F0K K.s (w'.D Z'))) := by
  intro K B f T w B' f' T' w' hE Z Z' hk hk' v v' hB
  have hres := resCharW_of_below w w' Z Z' v v' hB
  have hm : B'.R.m = B.R.m := by rw [hE.1]
  refine (mem_W1F_forced_iff K.s w Z v).trans (Iff.trans ?_ (mem_W1F_forced_iff K.s w' Z' v').symm)
  rw [hm, hres]
  refine exists_congr fun j => and_congr_right fun hj => ?_
  rw [FK_enl K.s w w' Z Z' hE.1 hk hk' (j + 1) _ (Nat.succ_pos j) hj]

end GlobalTheory.Mem.Top.Bl
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem fvalP_eq_FK (D : D7) (L : SizeData₂ D) (j p : ℕ) :
    FvalP L j p = FK L.sc D j p := by
  have hg : (p ∈ L.gTypes) ↔ ∃ i, p = D.host.g i := by
    simp only [Formalism.BasicNotions.SizeData₂.gTypes, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  unfold FvalP FK
  by_cases h : ∃ i, p = D.host.g i
  · rw [if_pos (hg.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hg.mp h')), if_neg h]

theorem Fval_eq_FK : ∀ (D : D7) (L : SizeData₂ D) (j : ℕ) (v : D.what₂.places.Pl),
    Fval L j v = FK L.sc D j (D.what₂.places.resChar v) := by
  intro D L j v
  exact fvalP_eq_FK D L j _

theorem resChar_eq_plc (D : D7) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := by
  have hp : (D.what₂.places.resChar w).Prime := D.what₂.places.resChar_prime w
  have hmem := Formalism.L2.Col.att_resChar_mem D.what₂.places D.plEq D.val_eq w
  haveI : Nontrivial (𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) :=
    Ideal.Quotient.nontrivial_iff.2 (D.plEq w).isPrime.ne_top
  have h0 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    simpa using this
  have hdvd : ringChar (𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) ∣ D.what₂.places.resChar w :=
    ringChar.dvd h0
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1.symm

theorem ofRecord_Fj_succ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (hK : DV.KapDef D)
    (y : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) :
    (Formalism.L2.DIV.ofRecord D L Del h0).Fj ((j : ℕ) + 1) y = F0K L.sc D y j := by
  have h := Formalism.L2.DIV.ofRecord_Fval D L Del h0 hK (j := (j : ℕ) + 1) (Nat.le_add_left 1 _)
    (Nat.succ_le_of_lt j.isLt) (D.plEq.symm y)
  rw [Fval_eq_FK] at h
  have hc : D.what₂.places.resChar (D.plEq.symm y) = Formalism.EigenvalueLevelCeiling.plc y := by
    rw [resChar_eq_plc, Equiv.apply_symm_apply]
  unfold F0K Formalism.L2.DIV.NumDatum.Fj
  rw [h, hc]

end GlobalTheory.Mem.Top.Bl
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevQ

theorem princ_in_chart_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {a b T f : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E)
    (hG : G.reindex (finCongr h) (finCongr h) = 1) {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ (G.reindex (finCongr h) (finCongr h)) T f bad) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin a → E)) (hfg : Module.Finite (𝓞 E) (reL h Λ))
    (hsp : Submodule.span E (reL h Λ : Set (Fin b → E)) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : GL (Fin a) (E ⊗[F] v.adicCompletion F), x ∈ levelVL σ G v Λ →
      (∀ y ∈ Formalism.L2.Herm.locL v Λ, ∃ z ∈ Formalism.L2.Herm.locL v Λ,
        (x : Matrix (Fin a) (Fin a) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (n : E ⊗[F] v.adicCompletion F) • z) →
      x ∈ (S.Uloc v).comap (reGL h (E ⊗[F] v.adicCompletion F)).toMonoidHom := by
  subst h
  have hR : ∀ (L : Submodule (𝓞 E) (Fin a → E)), reL rfl L = L := by
    intro L
    ext x
    simp [reL, reV]
  have hGr : G.reindex (finCongr rfl) (finCongr rfl) = G := by
    ext i j; simp
  rw [hR] at hfg hsp
  obtain ⟨M, hM, hMU⟩ := GlobalTheory.Mem.Col2.AdT.Opn.exists_princ_loc_step σ S v hG
  obtain ⟨d, hd, hdA⟩ := GlobalTheory.PrincLat.princ_lat v Λ (Module.Finite.iff_fg.1 hfg) hsp
  refine ⟨M * d, Nat.mul_pos hM hd, fun x hx hpr => ?_⟩
  have hxe : reGL rfl (E ⊗[F] v.adicCompletion F) x = x := by
    apply Units.ext
    ext i j
    simp [reGL]
  show reGL rfl (E ⊗[F] v.adicCompletion F) x ∈ S.Uloc v
  rw [hxe]
  refine hMU x ?_ (hdA M _ hpr)
  have hu : x ∈ UPts σ G (v.adicCompletion F) := hx.1
  rw [hGr]
  exact hu

theorem chart_contains_princ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hUloc hchi Lb0 hLb β v hv
  have hG := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
  have hfg : Module.Finite (𝓞 (I.rec7 l Z).host.E) (reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0) := by
    rw [← hLb]; exact (F u).levJ.Lb_fin
  have hsp : Submodule.span (I.rec7 l Z).host.E
      (reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 : Set (Fin ((I.rec7 l Z).R.N (B.R.m - 1)) → (I.rec7 l Z).host.E)) = ⊤ := by
    rw [← hLb]; exact (F u).levJ.Lb_span
  obtain ⟨n, hn, hN⟩ := princ_in_chart_gen (sigD (I.rec7 l Z)) (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _))
    ((I.rec7 l Z).sp.X (B.R.m - 1)).gram hG (K β).lev v Lb0 hfg hsp
  exact ⟨n, hn, fun x hx => hN x hx.1 hx.2⟩

end GlobalTheory.Mem.Col2.AdT.LevQ

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.DnAdel

theorem grpId {G : Type*} [Group G] (a b c d : G) : a * (a⁻¹ * b * c * d⁻¹) * d = b * c := by group

theorem grpId2 {G : Type*} [Group G] (r y1 kb y0 hm m : G) (h : hm = r * (y1 * kb)) :
    r * y1 = y0 * (y0⁻¹ * hm * m⁻¹ * hm⁻¹ * y0) * (y0⁻¹ * hm * m * kb⁻¹) := by subst h; group

theorem etaFacts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (v0 : HeightOneSpectrum (𝓞 F))
    (y0 hm g0 : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))
    (hy0 : y0 ∈ Formalism.L2.Herm.UstdAf hc n) (hh : hm ∈ Formalism.L2.Herm.UstdAf hc n) (hg : g0 ∈ Formalism.L2.Herm.UstdAf hc n) :
    (∀ v', v' ≠ v0 → bc (prV (E := E) v') (y0⁻¹ * hm * (rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * g0)))⁻¹ * hm⁻¹ * y0) = 1) ∧
      y0⁻¹ * hm * (rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * g0)))⁻¹ * hm⁻¹ * y0 ∈ Formalism.L2.Herm.UstdAf hc n := by
  have hm0 : rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * g0)) ∈ Formalism.L2.Herm.UstdAf hc n :=
    rll_put_mem_UAd hc n v0 (afsplit_bc_mem hc.sig 1 v0 _ (mul_mem (inv_mem hh) hg))
  refine ⟨fun v' hv' => ?_, ?_⟩
  · simp only [map_mul, map_inv]
    rw [rll_put_ne n v0 v' hv']
    group
  · exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hy0) hh) (inv_mem hm0)) (inv_mem hh)) hy0

theorem coreMove {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1)
    (v0 : HeightOneSpectrum (𝓞 F)) (U : Subgroup (GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))))
    (chi : U →* ℂˣ) (y0 y1 : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (kb : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (t s : ℂ) (hts : t = s⁻¹)
    (hk : kb ∈ Formalism.L2.Herm.UstdAf hc n)
    (hh : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) ∈ Formalism.L2.Herm.UstdAf hc n)
    (hlev : ∀ x, y0.1 * x * kb = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) *
        rll_put n v0 (bc (prV (E := E) v0) ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb))⁻¹ * (y0.1 * kb))) → x ∈ U)
    (hchi : ∀ x : U, y0.1 * x.1 * kb = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) *
        rll_put n v0 (bc (prV (E := E) v0) ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb))⁻¹ * (y0.1 * kb))) →
        ((chi x : ℂˣ) : ℂ) = t) :
    ∃ (η : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (κ : U), (∀ v', v' ≠ v0 → bc (prV (E := E) v') η.1 = 1) ∧
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y1.1 = y0.1 * η.1 * κ.1 ∧ (((chi κ)⁻¹ : ℂˣ) : ℂ) = s := by
  subst hJ
  set hm := bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) with hhm
  set m := rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * (y0.1 * kb))) with hmdef
  have hE := etaFacts hc n v0 y0.1 hm (y0.1 * kb) y0.2 hh (mul_mem y0.2 hk)
  have hx : y0.1 * (y0.1⁻¹ * hm * m * kb⁻¹) * kb = hm * m := grpId _ _ _ _
  have hU := hlev _ hx
  refine ⟨⟨_, hE.2⟩, ⟨_, hU⟩, hE.1, grpId2 _ _ _ _ _ _ hhm, ?_⟩
  rw [Units.val_inv_eq_inv_val, hchi ⟨_, hU⟩ hx, hts, inv_inv]

theorem actSameOff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (v : HeightOneSpectrum (𝓞 F)) {d d' : Deco E n ST SG}
    (h : Deco.SameOff ST SG v d d') (ga : Sp E n ≃ₗ[E] Sp E n) (hh : GLG (E := E) (n := n) (SG := SG)) :
    Deco.SameOff ST SG v (d.act ga hh) (d'.act ga hh) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    ext x
    show x ∈ localization₂ Q.asIdeal (gmap ga d.N) ↔ x ∈ localization₂ Q.asIdeal (gmap ga d'.N)
    rw [mem_localization_gmap, mem_localization_gmap, h.N Q hQ]
  · intro Q hQ
    funext x
    show d.f Q (ga.symm x) = d'.f Q (ga.symm x)
    rw [h.f Q hQ]
  · intro w hw
    funext x
    show (hh w).1.mulVec (d.be w (ga.symm x)) = (hh w).1.mulVec (d'.be w (ga.symm x))
    rw [h.be w hw]

theorem pointGen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 E)))
    (v0 : HeightOneSpectrum (𝓞 F)) (r0 d r' : DecoF E n ST SG Q) (a : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q)
    (hmv : a • r' = d) (hfr : d.fr = r0.fr) (hoff : Deco.SameOff ST SG v0 r0.deco.1 d.deco.1)
    (hQSQ : Q ⊆ SQ) (hdis : Disjoint SG Q) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F)))
    (h0 : IsPtOf hc g0 (extTo SQ r0))
    (h1 : IsPtOf hc h (((a.1, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n SQ) • extTo SQ r'))
    (hQ : ∀ P ∈ Q, ¬ IsOver v0 P) (hSG : ∀ w ∈ SG, ¬ IsOver v0 w) :
    IsPtOf hc (h * rll_put n v0 (bc (prV (E := E) v0) (h⁻¹ * g0)))
      ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • r0) := by
  have e1 : (((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • d = ((a.1, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • r' := by
    rw [← hmv, smul_smul]
    congr 1
    ext1
    · simp
    · ext1 <;> simp
  refine GlobalTheory.T.isPointOf_decoratedLattice_splicedAtPlace hc n ST SG Q SQ SQ v0 g0 h (extTo SQ r0) _ _ h0 h1 hQ hSG ?_ ?_ ?_ ?_
  · have h2 := actSameOff v0 hoff (((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q)).1.1) (((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q)).2.1)
    have e2 : (((a.1, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n SQ) • extTo SQ r').deco.1 = ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • d).deco.1 := by
      rw [e1]; rfl
    rw [e2]
    exact h2
  · intro P _
    ext x
    show x ∈ localization₂ P.asIdeal (gmap _ r0.deco.1.N) ↔ x ∈ localization₂ P.asIdeal r0.deco.1.N
    rw [mem_localization_gmap]
    exact Iff.rfl
  · intro P _
    funext x
    rfl
  · intro P
    refine ⟨⟨P.1, hQSQ P.2⟩, rfl, ?_⟩
    have hP : P.1 ∉ SG := Finset.disjoint_right.1 hdis P.2
    have e3 : ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • r0).fr P =
        ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • d).fr P := by
      show _ * r0.1.2 P * _ = _ * d.1.2 P * _
      rw [show d.1.2 P = d.fr P from rfl, hfr]; rfl
    rw [e3, e1]
    show a.1.1 * ptFr r' P.1 * _ = a.1.1 * r'.1.2 P * _
    rw [ptFr_of_mem r' hP P.2]
    simp
    rfl

theorem ufGL_UJ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : UF E n) : ufGL E n γ ∈ UJ (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) := by
  show cT _ _ * 1 * _ = 1
  rw [mul_one]
  exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul γ



theorem move_down_adelic : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ hβ : chOf ((I.fm l u a).dn i v c.1 g) = β, ∃ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)) (η : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (κ : (K β).lev.U), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) ∧ (∀ v', v' ≠ (eV v).1 → bc (prV (E := (I.rec7 l Z).host.E) v') η.1 = 1) ∧ bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) γ.1 * ((K β).y ⟨(I.fm l u a).dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧ ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) : B.LLˣ) : B.LL) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K eY eV L hR hY hV hL v β c g hg hβ
  obtain ⟨k, R⟩ := hR
  obtain ⟨c0, hc0⟩ := c
  subst hc0

  have hgram : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hOk hPins l Z).2.2.2 i hi).1
  haveI : NeZero (B.R.N i) := inferInstance
  have hP := GlobalTheory.T.levelPrimes_not_selfConjugate_disjoint_type_twist I hOk l u a v
  have hv0 : (eV v).1 = v.1.under (𝓞 B.host.F) := hV v
  have hd : ((I.atIn u a).A i).dnPt v c0 g = ((I.stp u a i).rep c0).mv (((I.stp u a i).rep c0).1.1.deco.dn v (TDat.extF _ v.1 g)) := rfl
  have hdn := GlobalTheory.T.moveDown_point_preserves_index_frames _ ((I.stp u a i).rep c0) v (TDat.extF _ v.1 g) (v.1.under (𝓞 B.host.F)) rfl hP.1 (IsOver.conj B.sp.cm rfl)
  rw [← hd, ← hv0] at hdn
  have hmv := (I.stp u a i).mv_smul c0.1 (((I.atIn u a).A i).dnPt v c0 g)
  have hyc' : ∀ (β' : Ch) (h : chOf ((I.fm l u a).dn i v c0 g) = β'), ((K β').y ⟨_, h⟩).1 = ((K (chOf ((I.fm l u a).dn i v c0 g))).y ⟨_, rfl⟩).1 := by rintro _ rfl; rfl
  have hk : k (chOf ((I.fm l u a).dn i v c0 g)) = k (chOf c0) := by rw [hβ]
  have hpt0 := R.pt c0
  have hpt1 := R.pt ((I.fm l u a).dn i v c0 g)
  rw [hk, ← hyc' _ hβ] at hpt1
  have hh := GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ B.sp.cm _ _ _ _ ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1 _ _ hpt1
  have hq := pointGen B.sp.cm (B.R.N i) _ _ _ I.SQ (eV v).1 _ _ _ (FrmG.incl _ _ ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g))) (congrArg (fun p => p.1.1) hmv) hdn.2.1 hdn.2.2 (I.Q_subset_SQ a) hP.2.2.2 _ _ hpt0 hh (hv0 ▸ hP.2.2.1) (hv0 ▸ hP.2.1)

  have hκ'mv : (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) * (I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g) = (((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1, 1) := by
    ext1
    · simp
    · simp
  have hgam1 : (I.stp u a i).gam c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) = 1 := by
    show ufGL _ _ ((1 : UF B.fields.E (B.R.N i))⁻¹) = 1
    simp
  have hchr : (I.stp u a i).chr c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) = ((I.stp u a i).chr c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)))⁻¹ := by
    rw [map_inv]; rfl

  have hc1 := GlobalTheory.T.couplingCoset_congr_index_frames_localLattices ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) ((I.stp u a i).rep c0)) ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) (((I.atIn u a).A i).dnPt v c0 g)) (by
      show (fun x => _) '' _ = (fun x => _) '' _
      rw [hdn.1]) (by
      funext P
      show _ * ((I.stp u a i).rep c0).1.1.1.2 P * _ = _ * (((I.atIn u a).A i).dnPt v c0 g).1.1.1.2 P * _
      rw [show (((I.atIn u a).A i).dnPt v c0 g).1.1.1.2 = (((I.atIn u a).A i).dnPt v c0 g).1.1.fr from rfl, hdn.2.1]
      rfl) (fun w => ⟨(actSameOff _ hdn.2.2 _ _).N w.1 (hv0 ▸ hP.2.1 w.1 w.2), (actSameOff _ hdn.2.2 _ _).be w (hv0 ▸ hP.2.1 w.1 w.2)⟩)
  have hc2 : (I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) (((I.atIn u a).A i).dnPt v c0 g) = (I.stp u a i).act c0.1 (((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1, 1) ((I.stp u a i).rep ((I.stp u a i).cl c0.1 (((I.atIn u a).A i).dnPt v c0 g))) := by
    unfold GStep.act
    rw [← hκ'mv]
    exact (congrArg (fun p => @HSMul.hSMul _ _ _ (@instHSMul _ _ ((I.stp u a i).actD c0.1).toSMul) (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) p) hmv).symm.trans (@mul_smul _ _ _ (@MulAction.toSemigroupAction _ _ _ ((I.stp u a i).actD c0.1)) _ _ _).symm
  have hc3 := GlobalTheory.T.couplingCosetInFrames_rational_action_eq I hOk l u a i c0.1 (((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1, 1) ((I.stp u a i).rep ((I.stp u a i).cl c0.1 (((I.atIn u a).A i).dnPt v c0 g))) rfl
  have hkey := ((R.key ((I.fm l u a).dn i v c0 g) c0).1 hβ).2
  have hcos : cosetIn ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) ((I.stp u a i).rep c0)) = cosetIn ((I.stp u a i).rep c0) := by
    rw [hc1, hc2, hc3]; exact hkey

  have hγU : (I.stp u a i).gam c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)) ∈ UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) := by
    rw [hgram]; exact ufGL_UJ B.sp.cm _ ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1
  have hts : B.embLL (((I.stp u a i).chr c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) : B.LLˣ) : B.LL) = (B.embLL (((I.stp u a i).chr c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)) : B.LLˣ) : B.LL))⁻¹ := by
    rw [hchr, Units.val_inv_eq_inv_val, map_inv₀]
  obtain ⟨kp, hkp, -⟩ := R.k_std (chOf c0)
  obtain ⟨η, κ, h1, h2, h3⟩ := coreMove B.sp.cm (B.R.N i) (gramN (I.rec7 l Z) i hi) hgram (eV v).1 ((K (chOf c0)).lev.U) ((K (chOf c0)).lev.chi) ((K (chOf c0)).y ⟨c0, rfl⟩) ((K (chOf c0)).y ⟨_, hβ⟩) ((I.stp u a i).gam c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g))) (k (chOf c0)) _ _ hts hkp.uni hh.uni (fun x hx => (R.lev c0 x ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) ((I.stp u a i).rep c0)).1.1 (by rw [hx]; exact hq)).2 ⟨(((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1), hgam1, rfl, hcos⟩) (fun x hx => R.chr c0 x (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) hgam1 (by rw [hx]; exact hq))
  exact ⟨⟨_, hγU⟩, η, κ, rfl, h1, h2, h3⟩

end GlobalTheory.Mem.Col2.DnAdel
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.AtDatumEvaluation

open GlobalTheory.Mem.Top.GroupRetwisting

theorem ev_scale {p : ℝ → ℝ → Prop} (h : ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, p eps x₀) :
    Ev fun K => ∃ x₀ : ℝ, x₀ ≤ K.s.x ∧ p K.s.eps x₀ :=
  ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    let ⟨x₀, hx⟩ := h eps h0
    ⟨x₀, fun _ _ _ _ hs hx' => ⟨x₀, hx', hs ▸ hx⟩⟩⟩⟩⟩⟩

theorem serClause_of_typesTrue (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) {P : Formalism.L2.Host.PiBar D.host} {W : Formalism.L2.Host.Omg D.host}
    (hT : TypesTrue D.ntypes P W) : SerClause D := by
  intro k
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hζ : Formalism.L2.NT.IsGenSys (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen := by
    intro d hd
    refine ⟨(GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order d hd, fun d' hdd hd' => ?_⟩
    obtain ⟨e, rfl⟩ := hdd
    exact (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_norm d e hd (Nat.pos_of_mul_pos_left hd')
  obtain ⟨O, -, -, hO⟩ := GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
    (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen hζ)
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact ⟨_, O, fun f => (hT.ser k f).trans (GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent hG _ _ _ _ _ (hT.teich k) O hO D.R.r f hr)⟩


end GlobalTheory.Mem.R3.Rw.AtDatumEvaluation

end
end
