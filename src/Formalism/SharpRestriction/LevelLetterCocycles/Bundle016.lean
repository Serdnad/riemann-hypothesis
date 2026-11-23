module

public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Comb

variable {n : ℕ} (a : ZMod n)

def sh {α : Type*} (f : ZMod n → α) : ZMod n → α := fun i => f (i - a)

def shC (cuts : Finset (ZMod n)) : Finset (ZMod n) := cuts.image (· + a)

theorem mem_shC {cuts : Finset (ZMod n)} {c : ZMod n} : c ∈ shC a cuts ↔ c - a ∈ cuts := by
  simp only [shC, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨c - a, h, sub_add_cancel c a⟩

theorem ellMax_sh (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    ellMax (shC a cuts) (sh a arcLen) = ellMax cuts arcLen := by
  unfold ellMax shC
  rw [Finset.sup_image]
  congr 1
  funext x
  simp [sh]

theorem cutsOK_sh {j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : CutsOK n j ty cuts arcLen) : CutsOK n j (sh a ty) (shC a cuts) (sh a arcLen) := by
  obtain ⟨hne, hj, h3, h4, h5⟩ := h
  refine ⟨hne.image _, hj, fun c hc ↦ ?_, fun c hc ↦ h4 _ ((mem_shC a).1 hc), fun c hc k hk1 hkj ↦ ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := h3 _ ((mem_shC a).1 hc)
    refine ⟨e1, e2, (mem_shC a).2 ?_, fun d hd1 hd2 hmem ↦ e4 d hd1 hd2 ?_⟩
    · rw [sub_right_comm]
      exact e3
    · have hm := (mem_shC a).1 hmem
      rwa [sub_right_comm] at hm
  · show ty (c + (k : ZMod n) - a) = LT.thin
    rw [show c + (k : ZMod n) - a = c - a + k by ring]
    exact h5 _ ((mem_shC a).1 hc) k hk1 hkj

theorem ro_sh (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) :
    ro (sh a ty) (sh a arcLen) c = ro ty arcLen (c - a) := by
  rw [Formalism.MainNotions.LocalTheoryWindows.ro, Formalism.MainNotions.LocalTheoryWindows.ro, Formalism.MainNotions.LocalTheoryWindows.thickLv, Formalism.MainNotions.LocalTheoryWindows.thickLv]
  congr 1
  apply Finset.filter_congr
  intro s _
  simp only [sh]
  rw [show c - (s : ZMod n) - a = c - a - s by ring]

theorem thickLe2_sh {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : ThickLe2 ty cuts arcLen) : ThickLe2 (sh a ty) (shC a cuts) (sh a arcLen) := by
  intro c hc
  rw [ro_sh]
  exact h _ ((mem_shC a).1 hc)

theorem wordOK_sh {l a₀ : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : WordOK l a₀ ty cuts arcLen) : WordOK l a₀ (sh a ty) (shC a cuts) (sh a arcLen) := by
  intro c hc s₀ s₁ hs hs1 b₀ b₁
  have h' := h _ ((mem_shC a).1 hc) s₀ s₁ hs hs1 b₀ b₁
  simp only [sh]
  rw [sub_right_comm c (s₁ : ZMod n) a, sub_right_comm c (s₀ : ZMod n) a]
  exact h'

theorem sizesOK_sh {g S h : ℕ} {ty : ZMod n → LT} (H : SizesOK g S h ty) :
    SizesOK g S h (sh a ty) := fun i ↦ H (i - a)

variable [NeZero n]

theorem Hmax_sh (H : ZMod n → ℕ) : Hmax n (sh a H) = Hmax n H := by
  unfold Hmax
  apply le_antisymm
  · exact Finset.sup_le fun i _ ↦ Finset.le_sup (f := H) (Finset.mem_univ (i - a))
  · refine Finset.sup_le fun i _ ↦ ?_
    have hle := Finset.le_sup (f := sh a H) (Finset.mem_univ (i + a))
    simpa [sh] using hle

theorem sBd_sh (l : ℕ) (H : ZMod n → ℕ) (i : ZMod n) : sBd l n (sh a H) i = sBd l n H (i - a) := by
  unfold sBd
  rw [Hmax_sh]
  congr 1
  funext k
  simp only [sh]
  rw [show i + ((k + 1 : ℕ) : ZMod n) - a = i - a + ((k + 1 : ℕ) : ZMod n) by ring]

theorem rF_sh (l : ℕ) (H : ZMod n → ℕ) (i : ZMod n) : rF l n (sh a H) i = rF l n H (i - a) := by
  unfold rF
  rw [sBd_sh, Hmax_sh]

theorem rrPar_sh (l : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) :
    rrPar l n (sh a H₁) (sh a H₂) (shC a cuts) = rrPar l n H₁ H₂ cuts := by
  unfold rrPar shC
  rw [Finset.sup_image]
  congr 1
  funext c
  simp [rF_sh]

theorem arc_parameters_shift_invariant (l j g h : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    initialExponentBound l n j g h (sh a H₁) (sh a H₂) (shC a cuts) (sh a arcLen) =
      initialExponentBound l n j g h H₁ H₂ cuts arcLen := by
  unfold initialExponentBound
  rw [rrPar_sh, ellMax_sh]

theorem ePar_sh (l j g h : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    ePar l n j g h (sh a H₁) (sh a H₂) (shC a cuts) (sh a arcLen) =
      ePar l n j g h H₁ H₂ cuts arcLen := by
  unfold ePar
  rw [rrPar_sh, arc_parameters_shift_invariant, ellMax_sh]

end Comb

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem jumpsAtE_sh (T : LocLat G Qp LL O) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (a i : ZMod n) (S : Set ℤ)
    (h : JumpsAtE PD T (fun k => emb (k + a)) (i - a) S) : JumpsAtE PD T emb i S := by
  intro τ hτ
  exact h τ (by simp only [sub_add_cancel]; exact hτ)

theorem exists_rot {emb emb' : ZMod n → (K₀ →ₐ[Qp] LL)} (hb : Function.Surjective emb')
    (h : ∀ i, (emb (i + 1)).comp PD.σ = emb i) (h' : ∀ i, (emb' (i + 1)).comp PD.σ = emb' i) :
    ∃ a : ZMod n, emb = fun i => emb' (i + a) := by
  obtain ⟨a, ha⟩ := hb (emb 0)
  refine ⟨a, ?_⟩
  have key : ∀ k : ℕ, emb (-(k : ZMod n)) = emb' (-(k : ZMod n) + a) := by
    intro k
    induction k with
    | zero => simp [ha]
    | succ k ih =>
      have e1 := h (-((k + 1 : ℕ) : ZMod n))
      have e2 := h' (-((k + 1 : ℕ) : ZMod n) + a)
      rw [show -((k + 1 : ℕ) : ZMod n) + 1 = -(k : ZMod n) by push_cast; ring, ih] at e1
      rw [show -((k + 1 : ℕ) : ZMod n) + a + 1 = -(k : ZMod n) + a by push_cast; ring] at e2
      rw [← e1, e2]
  funext i
  have hi := key ((-i).val)
  rwa [ZMod.natCast_zmod_val, neg_neg] at hi

variable [Fintype (K →ₐ[Qp] LL)]

theorem thmELiftAt_rot (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (a : ZMod n)
    (H : ThmELiftAt PD (O := O) n emb v) : ThmELiftAt PD (O := O) n (fun i => emb (i + a)) v := by
  intro hLet hp T₁ T₂ F hGood hC1 hC2 hOnto j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hKind hJ hg
    hSizes hCuts hThick hJ1 hJ2 hWord
  have hLet' : Letters PD LL v emb := by
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hLet
    refine ⟨e1, e2, e3, ?_, fun i ↦ ?_, e6⟩
    · have he : emb = (fun i ↦ emb (i + a)) ∘ (fun i ↦ i - a) := funext fun i ↦ by simp
      rw [he]
      exact e4.comp (Equiv.subRight a).bijective
    · have e := e5 (i - a)
      simp only [sub_add_cancel, show i - a + 1 + a = i + 1 by ring] at e
      exact e
  have hW : WordOK PD.p (initialExponentBound PD.p n j (gPar Gp S η) h (sh a Mb₁ + sh a hb₁) (sh a Mb₂ + sh a hb₂)
      (shC a cuts) (sh a arcLen)) (sh a ty) (shC a cuts) (sh a arcLen) := by
    rw [show sh a Mb₁ + sh a hb₁ = sh a (Mb₁ + hb₁) from rfl,
      show sh a Mb₂ + sh a hb₂ = sh a (Mb₂ + hb₂) from rfl, arc_parameters_shift_invariant]
    exact wordOK_sh a hWord
  have hL := H hLet' hp T₁ T₂ F hGood hC1 hC2 hOnto j Gp S η h (sh a ty) (shC a cuts) (sh a arcLen)
    (sh a Mb₁) (sh a hb₁) (sh a Mb₂) (sh a hb₂) (fun i ↦ jumpsAtE_sh T₁ emb a i _ (hKind (i - a))) hJ hg
    (sizesOK_sh a hSizes) (cutsOK_sh a hCuts) (thickLe2_sh a hThick)
    (fun i ↦ jumpsAtE_sh T₁ emb a i _ (hJ1 (i - a))) (fun i ↦ jumpsAtE_sh T₂ emb a i _ (hJ2 (i - a))) hW
  rwa [show sh a Mb₁ + sh a hb₁ = sh a (Mb₁ + hb₁) from rfl,
    show sh a Mb₂ + sh a hb₂ = sh a (Mb₂ + hb₂) from rfl, ePar_sh] at hL

end Formalism.MainNotions.WachCoordinates.Br
end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX TCase)
open Formalism.MainNotions.LiftingTheory (qp pk Over CaseA JumpsLet)
open Formalism.MainNotions.WachCoordinates (FilLev)
open Formalism.MainNotions.DeltaInvariantLattices (ιDi)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def conv {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (k - j)

def IsExp (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : W.DD T)
    (d : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  (∃ m : ℤ, ∀ k < m, d k = 0) ∧ ∃ (a : LetA O n) (ha : a • x ∈ W.N T), W.lev i ζ a ≠ 0 ∧
    ∀ k : ℤ, W.levN T i ζ ⟨a • x, ha⟩ k = conv (W.lev i ζ a) d k

def ExpRing (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    (∃ u : PowerSeries LL, IsUnit u ∧ W.lev i ζ (qp W) = u * PowerSeries.X) ∧
    PowerSeries.constantCoeff (W.lev i ζ W.π₀) = -(PD.p : LL) ∧ IsUnit (W.lev i ζ (pk W 1))

def ExpRules (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    (∀ (x : W.DD T) (a : LetA O n), a • x ∈ W.N T → W.lev i ζ a ≠ 0 → ∃! d, IsExp W T i ζ x d) ∧
    (∀ x d, DL W T i x → IsExp W T i ζ x d → ∀ k, d k ∈ ιDi W T i) ∧
    (∀ x y d e, IsExp W T i ζ x d → IsExp W T i ζ y e → IsExp W T i ζ (x + y) (d + e)) ∧
    (∀ (c : O) x d, IsExp W T i ζ x d → IsExp W T i ζ (c • x) (fun k => algebraMap O LL c • d k)) ∧
    (∀ (a : LetA O n) x d, IsExp W T i ζ x d → IsExp W T i ζ (a • x) (conv (W.lev i ζ a) d)) ∧
    (∀ x d, IsExp W T i ζ x d →
      IsExp W T i ζ (W.γ T x) (fun k => (algebraMap O LL (W.χΓ W.gam : O)) ^ k • d k)) ∧
    ∀ (T' : LocLat G Qp LL O) (F : LatHom T.L T'.L), IsCrys PD T'.ρ → ∀ x d, IsExp W T i ζ x d →
      IsExp W T' i ζ (W.map F x)
        (fun k => AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR) (d k))

def ExpCrit (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), DL W T i x → IsExp W T i ζ x d →
      ((∃ k : ℕ, qp W ^ k • x ∈ W.N T) → (x ∈ W.N T ↔ ∀ k, d k ∈ FilLev W T i 0 (-k))) ∧
      ((∃ k : ℕ, qp W ^ k • x ∈ pullJ W T (i - 1) 1) → (x ∈ pullJ W T (i - 1) 1 ↔ ∀ k < 0, d k = 0))

def LemK (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), DL W T i x → IsExp W T i ζ x d →
      (∃ j : ℕ, ((PD.p : ℕ) : O) ^ j • (W.γ T x - x) ∈ W.N T) →
      (∀ k, k ≠ 0 → d k ∈ FilLev W T i 0 (-k)) ∧
      ∀ y : ℕ, qp W ^ y • x ∈ W.N T →
        d 0 ∈ FilLev W T i 0 (-(y : ℤ)) ∧ (x ∈ W.N T ↔ d 0 ∈ FilLev W T i 0 0)

def FilDim (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Over W τ i →
    finrank LL ↥(ιDi W T i) = finrank LL T.V ∧
    ∀ a b : ℤ, a ≤ b → (finrank LL ↥(FilLev W T i 0 a) : ℤ) - finrank LL ↥(FilLev W T i 0 b) =
      ∑ u ∈ Finset.Ico a b, multV PD T.ρ τ u

def at0 (W : LocWach PD LL O v n) (f : PowerSeries O) : LetA O n := fun _ => PowerSeries.subst W.π₀₁ f

def IsBas (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) {r : ℕ} (e : Fin r → W.DD T) : Prop :=
  (∀ k, e k ∈ W.N T ∧ DL W T i (e k)) ∧
    ∀ x ∈ W.N T, DL W T i x → ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • e k

def BasTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ i : ZMod n,
    (∃ e : Fin (finrank LL T.V) → W.DD T, IsBas W T i e) ∧
    ∀ (r : ℕ) (e : Fin r → W.DD T), IsBas W T i e → ∀ j : ℕ,
      (∀ x ∈ pullJ W T i j, DL W T (i + (j : ZMod n)) x →
        ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • ((W.φD T) ^ j) (e k)) ∧
      ∀ (x : W.DD T) (s : ℕ), ((PD.p : ℕ) : O) ^ s • x ∈ pullJ W T i j → x ∈ pullJ W T i j

def DetTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ → JumpsLet W T Mi hi →
    ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Over W τ i → ∀ (r : ℕ) (e e' : Fin r → W.DD T),
      IsBas W T i e → IsBas W T (i - 1) e' → ∀ (M : ℕ) (P : Matrix (Fin r) (Fin r) (PowerSeries O)),
        (∀ k, qp W ^ M • W.φD T (e' k) = ∑ m, at0 W (P m k) • e m) →
        ∃ (u : PowerSeries O) (w : ℕ), IsUnit u ∧
          P.det = u * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ w ∧
          (w : ℤ) = (M : ℤ) * r + ∑ a ∈ Finset.Icc (-(Mi i : ℤ)) (hi i : ℤ), a * multV PD T.ρ τ a

def ZTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → 11 ≤ PD.p → ∀ (j X σ : ℕ), TCase PD.p j 1 X σ →
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (r : ℕ) (e : Fin r → W.DD T) (he : IsBas W T i e),
      ∃ Z Z' R : Matrix (Fin r) (Fin r) (PowerSeries O),
        (∀ m k, PowerSeries.constantCoeff (Z m k) = if m = k then ((PD.p : ℕ) : O) ^ σ else 0) ∧
        Z * Z' = ((PD.p : ℕ) : PowerSeries O) ^ (2 * σ) • (1 : Matrix (Fin r) (Fin r) (PowerSeries O)) +
          (PowerSeries.X * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ X) • R ∧
        ∀ k, (∃ p ∈ pullJ W T i j,
            W.γ T (∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m)) - ∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m) =
              fMX W 1 X • p) ∧
          ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ d,
            IsExp W T (i + (j : ZMod n)) ζ (∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m)) d →
            ∀ s : ℤ, s < X → d s = if s = 0 then (PD.p : LL) ^ σ • ιV PD (LL := LL) (V := T.V)
              ((φVB PD (LL := LL) (V := T.V))^[j] (W.cmp T ⟨e k, (he.1 k).1⟩)) else 0

def ExtData (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ) (a N : ℕ) {FF : Type} [AddCommGroup FF]
    [Module O FF] (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T.L)) (y z : FF →ₗ[O] W.DD T) (μ ν : ZMod n → FF →ₗ[O] W.DD T) : Prop :=
  (∀ f, ∃ (x : ↥(W.wachCocyclesDelta T)) (hκ : (g f : G → T.V) ∈ latticeCocycles T.L), (x : W.DD T × W.DD T) = (y f, z f) ∧
    W.clK T x = Submodule.Quotient.mk (⟨(g f : G → T.V), hκ⟩ : ↥(latticeCocycles T.L))) ∧
  ∀ (i : ZMod n) (f : FF), DL W T i (μ i f) ∧ DL W T i (ν i f) ∧
    InPN W T 1 (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z f) + (W.γ T (μ i f) - μ i f)) ∧
    qp W ^ Mi i • (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f) + W.φD T (μ (i - 1) f) - μ i f) ∈ W.N T ∧
    (∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • (qp W ^ hi i •
      (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f) + W.φD T (μ (i - 1) f) - μ i f)) ∈
        pullJ W T (i - 1) 1) ∧
    ((PD.p : ℕ) : O) ^ N • ν i f - qp W ^ a • μ i f ∈ W.N T

def ExtTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)),
      ∃ (N : ℕ) (y z : FF →ₗ[O] W.DD T₂) (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
        ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

section

noncomputable section

namespace Formalism.MainNotions.IntegralHeckeForms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

variable {Y}

variable (Y)

variable {Y}

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

open NumberField Formalism.BasicNotions

def TwistedAt (D : D7) (w : D.what₂.places.Pl) : Prop := D.what₂.muAt w ≠ D.what₂.mu0

theorem twistedAt_conj (D : D7) (w : D.what₂.places.Pl) : TwistedAt D (D.what₂.places.conj w) ↔ TwistedAt D w := by
  unfold TwistedAt
  rw [D.what₂.muAt_conj]

structure TwIn (D : D7) where
  E : IntegralHeckeForms.XD D
  N0 : D.ntw.Tw → ℕ
  S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)

def TwIn.Sg {D : D7} (I : TwIn D) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Set (D.nexp.Dat i j b) :=
  IntegralHeckeForms.SgJ D.nexp I.E i j b

def TwIn.Ok {D : D7} (I : TwIn D) (i : D.ntw.Tw) : Prop :=
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp I.E i j b (I.Sg i j b)) ∧
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (I.Sg i j b) (I.S i j b))

def twEps (D : D7) (i : D.ntw.Tw) : ℝ := ((D.ntw.l i : ℝ) ^ 2)⁻¹

theorem twEps_pos (D : D7) (i : D.ntw.Tw) : 0 < twEps D i := by
  unfold twEps
  have hl : (0 : ℝ) < (D.ntw.l i : ℝ) := by exact_mod_cast (D.ntw.lPrime i).out.pos
  positivity

def rPrAv (D : D7) : ℕ :=
  sInf {p : ℕ | p.Prime ∧
    ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK}

def q0Av (D : D7) : ℕ := sInf {p : ℕ | p.Prime ∧ p % (rPrAv D * LevelStarExponents.condE D) = 1 ∧ ¬ p ∣ Ideal.absNorm D.host.ccK}

def avPrimes (D : D7) : Finset ℕ :=
  letI := D.wordFin
  ((insert 3 (insert 5 (insert (D.host.g 0) (insert (D.host.g 1) (insert D.host.pde (insert D.host.pde'
    (insert (q0Av D) (Finset.univ.image fun u => (D.mem u).A.T)))))))) ∪
    (Ideal.absNorm D.host.ccK).primeFactors).filter (· ≠ 0)

def AvSet (D : D7) : Set (PlE D.host) := ⋃ p ∈ avPrimes D, placesOver D.host.E p

theorem placesOver_finite_av (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have hI : (Ideal.span {((p : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem avSet_finite (D : D7) : (AvSet D).Finite := by
  unfold AvSet
  exact Set.Finite.biUnion (Finset.finite_toSet _) fun p hp =>
    placesOver_finite_av _ p (Finset.mem_filter.mp hp).2

def AvRec (D : D7) : Finset (PlE D.host) := (avSet_finite D).toFinset

theorem mem_avRec {D : D7} (v : PlE D.host) : v ∈ AvRec D ↔ ∃ p ∈ avPrimes D, v ∈ placesOver D.host.E p := by
  simp only [AvRec, AvSet, Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop]


open Classical in
def TwGoodOne (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 i (twEps D i) (I.S i) (AvRec D) Q k' (BlochKatoReduction.Gen.psiAt b ψ)

def TwGoodAt (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    I.Ok (C.twI w) ∧ TwGoodOne D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

abbrev TwPack (D : D7) : Type :=
  Σ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k' : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ

def twPack (D : D7) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : TwPack D :=
  ⟨i, Q, k', BlochKatoReduction.Gen.psiAt b ψ⟩

def NChoicePack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D :=
  twPack D (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

def TwConjAt (D : D7) (C : NChoice D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    NChoicePack C (D.what₂.places.conj w) = NChoicePack C w ∧
      (D.what₂.places.conj w ≠ w → C.sd (D.what₂.places.conj w) = !C.sd w)

def TwGoodE {eps : ℝ} (Fm : FamP eps) (E : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, IntegralHeckeForms.XD (Fm.D x i)) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
      ∃ (N0 : (Fm.D x i).ntw.Tw → ℕ) (S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)),
        TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch ⟨E x hx i, N0, S⟩

def twEOf {D : D7} (T : ThData D) : IntegralHeckeForms.XD D := ⟨T.xd0, T.thetaBase_invariant_action⟩

def twE {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : IntegralHeckeForms.XD (Fm.D x i) := twEOf (Fm.ex x hx i).xd

def TwGood {eps : ℝ} (Fm : FamP eps) : Prop := TwGoodE Fm (twE Fm)

theorem psiAt_psiAt {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) :
    BlochKatoReduction.Gen.psiAt b (BlochKatoReduction.Gen.psiAt b ψ) = ψ := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]


end Formalism.MainNotions

end
end
