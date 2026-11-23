module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle536
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle506
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgC
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle005
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem collect {α β : Type} (S : Finset α) (X : Set β) (Q : α → Finset β → Prop)
    (hmono : ∀ a (F F' : Finset β), F ⊆ F' → Q a F → Q a F')
    (h : ∀ a ∈ S, ∃ F : Finset β, (↑F : Set β) ⊆ X ∧ Q a F) :
    ∃ F : Finset β, (↑F : Set β) ⊆ X ∧ ∀ a ∈ S, Q a F := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨F, hF, hQ⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨F', hF', hQ'⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨F ∪ F', by rw [Finset.coe_union]; exact Set.union_subset hF hF', fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hmono _ _ _ Finset.subset_union_right hQ'
    · exact hmono _ _ _ Finset.subset_union_left (hQ b hb)

theorem finGL_unip' {N k : ℕ} (x : BlockIx N k → Af E) :
    finGL E N (unip x) = unip (fun p => sFin E (x p)) := by
  apply Units.ext
  change 1 - (1 : Matrix (Fin N) (Fin N) (Af E)).map (sFin E) + (1 + nilM x).map (sFin E) = 1 + nilM _
  rw [Matrix.map_add _ (map_add (sFin E))]
  have : (nilM x).map (sFin E) = nilM (r := k) (fun p => sFin E (x p)) := by
    ext i j
    simp only [nilM, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [this]; abel

theorem cover (L : Subgroup (GL (Fin (r + s)) (Af E))) (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E)))) :
    ∃ Tf : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GL (Fin (r + s)) (Af E),
      ∃ (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t l : GL (Fin (r + s)) (Af E)),
        t ∈ Tf ∧ l ∈ L ∧ g = unip x * lev (Af E) r s (a, b) * t * l := by
  obtain ⟨Tf, hTf⟩ := IwaAd.exists_finset_cover E (r + s) L hL
  refine ⟨Tf, fun g => ?_⟩
  obtain ⟨x, m, c, hc, rfl⟩ := IwaFin.exists_unip_lev_integral E r s g
  obtain ⟨t, ht, l, hl, rfl⟩ := hTf c hc
  exact ⟨x, m.1, m.2, t, l, ht, hl, by rw [← mul_assoc]⟩

theorem yp_decomp (k : Kinf E (r + s)) (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E))
    (b : GL (Fin s) (Af E)) (t l : GL (Fin (r + s)) (Af E)) :
    BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l) =
      unip (fun p => sFin E (x p)) * lev (Ad E) r s (finGL E r a, finGL E s b) * BlockDerivatives.yp k t * finGL E (r + s) l := by
  have hP : finGL E (r + s) (unip x * lev (Af E) r s (a, b)) =
      unip (fun p => sFin E (x p)) * lev (Ad E) r s (finGL E r a, finGL E s b) := by
    rw [map_mul, finGL_unip', Slice1.lev_finGL]
  rw [← hP, BlockDerivatives.yp, BlockDerivatives.yp]
  have e : finGL E (r + s) (unip x * lev (Af E) r s (a, b) * t * l) =
      finGL E (r + s) (unip x * lev (Af E) r s (a, b)) * finGL E (r + s) t * finGL E (r + s) l := by
    rw [map_mul, map_mul]
  rw [e]
  simp only [mul_assoc]
  rw [← mul_assoc (infGL E (r + s) (Unitary.toUnits k)) (finGL E (r + s) (unip x * lev (Af E) r s (a, b))),
    infGL_comm, mul_assoc]

theorem yp_one_fin {a : ℕ} (h : GL (Fin a) (Af E)) : BlockDerivatives.yp (1 : Kinf E a) h = finGL E a h := by
  simp [BlockDerivatives.yp]

theorem grp_step (m : GA E r × GA E s) (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E))
    (y : GA E (r + s)) (z : GA E (r + s)) :
    ∃ v : BlockIx (r + s) r → Ad E, lev (Ad E) r s m * (unip (fun p => sFin E (x p)) *
        lev (Ad E) r s (finGL E r a, finGL E s b) * y * z) =
      unip v * (lev (Ad E) r s (m.1 * finGL E r a, m.2 * finGL E s b) * y) * z := by
  obtain ⟨v, hv⟩ := InducedTensorMap.lev_mul_unip m (fun p => sFin E (x p))
  refine ⟨v, ?_⟩
  have e : lev (Ad E) r s (m.1 * finGL E r a, m.2 * finGL E s b) =
      lev (Ad E) r s m * lev (Ad E) r s (finGL E r a, finGL E s b) := by
    rw [← map_mul]; rfl
  rw [e]
  simp only [mul_assoc]
  rw [← mul_assoc (lev (Ad E) r s m) (unip _), hv]
  simp only [mul_assoc]

theorem slice_decomp_left (F : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (l : GL (Fin (r + s)) (Af E)) (hl : ∀ y, F.1 (y * finGL E (r + s) l) = F.1 y) (k : Kinf E (r + s))
    (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t : GL (Fin (r + s)) (Af E))
    (m₂ : GA E s) :
    sl0 m₂ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F) =
      act (.fin a) (sl0 (m₂ * finGL E s b) (rt E (r + s) (BlockDerivatives.yp k t) F)) := by
  refine Subtype.ext (funext fun m₁ => ?_)
  have L : (sl0 m₂ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F)).1 m₁ =
      F.1 (lev (Ad E) r s (m₁, m₂) * BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) := by
    rw [left_slice_apply, rt_apply]
  have R : (act (.fin a) (sl0 (m₂ * finGL E s b) (rt E (r + s) (BlockDerivatives.yp k t) F))).1 m₁ =
      F.1 (lev (Ad E) r s (m₁ * finGL E r a, m₂ * finGL E s b) * BlockDerivatives.yp k t) := by
    rw [act_fin_eq, rt_apply, yp_one_fin, left_slice_apply, rt_apply]
  rw [L, R, yp_decomp]
  obtain ⟨v, hv⟩ := grp_step (m₁, m₂) x a b (BlockDerivatives.yp k t) (finGL E (r + s) l)
  rw [hv, hl, hu]

theorem slice_decomp_right (F : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (l : GL (Fin (r + s)) (Af E)) (hl : ∀ y, F.1 (y * finGL E (r + s) l) = F.1 y) (k : Kinf E (r + s))
    (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t : GL (Fin (r + s)) (Af E))
    (m₁ : GA E r) :
    sl1 m₁ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F) =
      act (.fin b) (sl1 (m₁ * finGL E r a) (rt E (r + s) (BlockDerivatives.yp k t) F)) := by
  refine Subtype.ext (funext fun m₂ => ?_)
  have L : (sl1 m₁ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F)).1 m₂ =
      F.1 (lev (Ad E) r s (m₁, m₂) * BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) := by
    rw [right_slice_apply, rt_apply]
  have R : (act (.fin b) (sl1 (m₁ * finGL E r a) (rt E (r + s) (BlockDerivatives.yp k t) F))).1 m₂ =
      F.1 (lev (Ad E) r s (m₁ * finGL E r a, m₂ * finGL E s b) * BlockDerivatives.yp k t) := by
    rw [act_fin_eq, rt_apply, yp_one_fin, right_slice_apply, rt_apply]
  rw [L, R, yp_decomp]
  obtain ⟨v, hv⟩ := grp_step (m₁, m₂) x a b (BlockDerivatives.yp k t) (finGL E (r + s) l)
  rw [hv, hl, hu]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

def HExp (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Prop :=
  ∀ ψ ∈ U, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s),
    (∀ i, b i ∈ Submodule.span ℂ (BlockDerivatives.lsF r s (T ψ) k g)) ∧ (∀ i, q i ∈ BlockDerivatives.rsF r s (T ψ) k g) ∧
    ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m * BlockDerivatives.yp k g) = ∑ i, (b i).1 m.1 * (q i).1 m.2

theorem lsF_yp (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∀ ℓ ∈ BlockDerivatives.lsF r s F k g, ∃ m₂, ℓ = sl0 m₂ (rt E (r + s) (BlockDerivatives.yp k g) F) := by
  rintro ℓ ⟨m₂, h⟩
  exact ⟨m₂, Subtype.ext (funext fun m₁ => by rw [h, left_slice_apply, rt_apply])⟩

theorem rsF_yp (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∀ ℓ ∈ BlockDerivatives.rsF r s F k g, ∃ m₁, ℓ = sl1 m₁ (rt E (r + s) (BlockDerivatives.yp k g) F) := by
  rintro ℓ ⟨m₁, h⟩
  exact ⟨m₁, Subtype.ext (funext fun m₂ => by rw [h, right_slice_apply, rt_apply])⟩

theorem rt_one {a : ℕ} (F : Sm E a) : rt E a (BlockDerivatives.yp 1 1) F = F := by
  rw [yp_one, map_one, Module.End.one_apply]

theorem lsF_one (F : Sm E (r + s)) : ∀ ℓ ∈ BlockDerivatives.lsF r s F 1 1, ∃ m₂, ℓ = sl0 m₂ F := by
  intro ℓ hℓ
  obtain ⟨m₂, h⟩ := lsF_yp F 1 1 ℓ hℓ
  exact ⟨m₂, by rw [h, rt_one]⟩

theorem rsF_one (F : Sm E (r + s)) : ∀ ℓ ∈ BlockDerivatives.rsF r s F 1 1, ∃ m₁, ℓ = sl1 m₁ F := by
  intro ℓ hℓ
  obtain ⟨m₁, h⟩ := rsF_yp F 1 1 ℓ hℓ
  exact ⟨m₁, by rw [h, rt_one]⟩

theorem exp_one {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hexp : HExp U T)
    {ψ : Sm E (r + s)} (hψ : ψ ∈ U) :
    ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s),
      (∀ i, b i ∈ Submodule.span ℂ (BlockDerivatives.lsF r s (T ψ) 1 1)) ∧ (∀ i, q i ∈ BlockDerivatives.rsF r s (T ψ) 1 1) ∧
      ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2 := by
  obtain ⟨n, b, q, hb, hq, he⟩ := hexp ψ hψ 1 1
  refine ⟨n, b, q, hb, hq, fun m => ?_⟩
  rw [← he m, yp_one, mul_one]

theorem rt_yp_eq {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (φ : Sm E a) :
    rt E a (BlockDerivatives.yp k g) φ = act (.cpt k) (act (.fin g) φ) := by
  rw [act_cpt_eq, act_fin_eq, rt_yp_rt, mul_one, one_mul]

theorem rt_yp_mem {a : ℕ} {U : Submodule ℂ (Sm E a)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) (k : Kinf E a) (g : GL (Fin a) (Af E))
    {φ : Sm E a} (hφ : φ ∈ U) : rt E a (BlockDerivatives.yp k g) φ ∈ U := by
  rw [rt_yp_eq]
  exact hU _ _ (hU _ _ hφ)

theorem T_rt_yp {a : ℕ} {U : Submodule ℂ (Sm E a)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) {T : Sm E a →ₗ[ℂ] Sm E a}
    (hT : ∀ o, ∀ φ ∈ U, T (act o φ) = act o (T φ)) (k : Kinf E a) (g : GL (Fin a) (Af E)) {φ : Sm E a}
    (hφ : φ ∈ U) : T (rt E a (BlockDerivatives.yp k g) φ) = rt E a (BlockDerivatives.yp k g) (T φ) := by
  rw [rt_yp_eq, rt_yp_eq, hT _ _ (hU _ _ hφ), hT _ _ hφ]

def Mleft (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W : Submodule ℂ (Sm E r)) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {ψ | ψ ∈ U ∧ ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
    sl0 m₂ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ)) ∈ W}
  add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun k g m₂ => by
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact W.add_mem (ha.2 k g m₂) (hb.2 k g m₂)⟩
  zero_mem' := ⟨U.zero_mem, fun k g m₂ => by rw [map_zero, map_zero, map_zero]; exact W.zero_mem⟩
  smul_mem' := fun c a ha => ⟨U.smul_mem c ha.1, fun k g m₂ => by
    rw [map_smul, map_smul, map_smul]; exact W.smul_mem c (ha.2 k g m₂)⟩

def Mright (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W : Submodule ℂ (Sm E s)) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {ψ | ψ ∈ U ∧ ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
    sl1 m₁ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ)) ∈ W}
  add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun k g m₁ => by
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact W.add_mem (ha.2 k g m₁) (hb.2 k g m₁)⟩
  zero_mem' := ⟨U.zero_mem, fun k g m₁ => by rw [map_zero, map_zero, map_zero]; exact W.zero_mem⟩
  smul_mem' := fun c a ha => ⟨U.smul_mem c ha.1, fun k g m₁ => by
    rw [map_smul, map_smul, map_smul]; exact W.smul_mem c (ha.2 k g m₁)⟩

theorem Mleft_stable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ}
    {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hT : IsSliceMap U c T) (hexp : HExp U T) (W : Submodule ℂ (Sm E r))
    (hW : _root_.GlobalTheory.CuspRep.IsStable W) : _root_.GlobalTheory.CuspRep.IsStable (Mleft U T W) := by
  rintro o ψ ⟨hψU, hψ⟩
  cases o with
  | fin h =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    rw [act_fin_eq, rt_yp_rt, mul_one]
    exact hψ k (g * h) m₂
  | cpt κ =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    rw [act_cpt_eq, rt_yp_rt, mul_one]
    exact hψ (k * κ) g m₂
  | lie X =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    obtain ⟨X', hX'⟩ := rt_lie_yp k g X
    have hψ'U : rt E (r + s) (BlockDerivatives.yp k g) ψ ∈ U := rt_yp_mem hU.1 k g hψU
    have e1 : rt E (r + s) (BlockDerivatives.yp k g) (act (.lie X) ψ) = lie E (r + s) X' (rt E (r + s) (BlockDerivatives.yp k g) ψ) :=
      LinearMap.congr_fun hX' ψ
    rw [e1]
    have e2 := hT.equiv (.lie X') _ hψ'U
    change T (lie E (r + s) X' _) = lie E (r + s) X' _ at e2
    rw [e2]
    set ψ' := rt E (r + s) (BlockDerivatives.yp k g) ψ with hψ'
    have hP : ∀ m₂, sl0 m₂ (T ψ') ∈ W := fun m₂ => hψ k g m₂
    obtain ⟨n, b, q, hb, -, he⟩ := exp_one hexp hψ'U
    have hsub : BlockDerivatives.lsF r s (T ψ') 1 1 ⊆ W := fun ℓ hℓ => by
      obtain ⟨m, rfl⟩ := lsF_one _ ℓ hℓ
      exact hP m
    have hbW : ∀ i, b i ∈ W := fun i => (Submodule.span_le.2 hsub) (hb i)
    rw [lie_split, map_add (f := _)]
    refine W.add_mem (key_left W hW (T ψ') (hT.unipInv ψ' hψ'U) hP b q hbW he _ (par_low X') m₂) ?_
    have e3 := hT.equiv (.lie (toL (skw X'))) _ hψ'U
    change T (lie E (r + s) (toL (skw X')) ψ') = lie E (r + s) (toL (skw X')) (T ψ') at e3
    rw [← e3]
    have : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan ψ') := (hU.2 ψ' hψ'U).kfin
    have hmem := lie_mem_orbSpan ψ' (skw X') (skw_skew X')
    have hle : GlobalTheory.CuspRep.LocEx.orbSpan ψ' ≤ W.comap (sl0 m₂ ∘ₗ T) := Submodule.span_le.2 (by
      rintro _ ⟨κ, rfl⟩
      change sl0 m₂ (T (act (.cpt κ) ψ')) ∈ W
      rw [act_cpt_eq, hψ', rt_yp_rt, one_mul]
      exact hψ (κ * k) g m₂)
    exact hle hmem

theorem Mright_stable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ}
    {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hT : IsSliceMap U c T) (hexp : HExp U T) (W : Submodule ℂ (Sm E s))
    (hW : _root_.GlobalTheory.CuspRep.IsStable W) : _root_.GlobalTheory.CuspRep.IsStable (Mright U T W) := by
  rintro o ψ ⟨hψU, hψ⟩
  cases o with
  | fin h =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    rw [act_fin_eq, rt_yp_rt, mul_one]
    exact hψ k (g * h) m₁
  | cpt κ =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    rw [act_cpt_eq, rt_yp_rt, mul_one]
    exact hψ (k * κ) g m₁
  | lie X =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    obtain ⟨X', hX'⟩ := rt_lie_yp k g X
    have hψ'U : rt E (r + s) (BlockDerivatives.yp k g) ψ ∈ U := rt_yp_mem hU.1 k g hψU
    have e1 : rt E (r + s) (BlockDerivatives.yp k g) (act (.lie X) ψ) = lie E (r + s) X' (rt E (r + s) (BlockDerivatives.yp k g) ψ) :=
      LinearMap.congr_fun hX' ψ
    rw [e1]
    have e2 := hT.equiv (.lie X') _ hψ'U
    change T (lie E (r + s) X' _) = lie E (r + s) X' _ at e2
    rw [e2]
    set ψ' := rt E (r + s) (BlockDerivatives.yp k g) ψ with hψ'
    have hP : ∀ m₁, sl1 m₁ (T ψ') ∈ W := fun m₁ => hψ k g m₁
    obtain ⟨n, b, q, -, hq, he⟩ := exp_one hexp hψ'U
    have hqW : ∀ i, q i ∈ W := fun i => by
      obtain ⟨m, hm⟩ := rsF_one _ _ (hq i)
      rw [hm]
      exact hP m
    rw [lie_split, map_add (f := _)]
    refine W.add_mem (key_right W hW (T ψ') (hT.unipInv ψ' hψ'U) hP b q hqW he _ (par_low X') m₁) ?_
    have e3 := hT.equiv (.lie (toL (skw X'))) _ hψ'U
    change T (lie E (r + s) (toL (skw X')) ψ') = lie E (r + s) (toL (skw X')) (T ψ') at e3
    rw [← e3]
    have : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan ψ') := (hU.2 ψ' hψ'U).kfin
    have hmem := lie_mem_orbSpan ψ' (skw X') (skw_skew X')
    have hle : GlobalTheory.CuspRep.LocEx.orbSpan ψ' ≤ W.comap (sl1 m₁ ∘ₗ T) := Submodule.span_le.2 (by
      rintro _ ⟨κ, rfl⟩
      change sl1 m₁ (T (act (.cpt κ) ψ')) ∈ W
      rw [act_cpt_eq, hψ', rt_yp_rt, one_mul]
      exact hψ (κ * k) g m₁)
    exact hle hmem

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end
