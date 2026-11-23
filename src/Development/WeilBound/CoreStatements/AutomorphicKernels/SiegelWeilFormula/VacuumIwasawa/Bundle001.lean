module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaCut
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacCut
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.FrameLin
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Mat

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Semiring R]

theorem mul_row_one {H : Matrix ι ι R} {u : ι} (hu : ∀ v, H u v = (1 : Matrix ι ι R) u v) (X : Matrix ι ι R) (e : ι) :
    (H * X) u e = X u e := by
  simp only [Matrix.mul_apply, hu, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

theorem mul_col_one {H : Matrix ι ι R} {u : ι} (hu : ∀ v, H v u = (1 : Matrix ι ι R) v u) (X : Matrix ι ι R) (e : ι) :
    (X * H) e u = X e u := by
  simp only [Matrix.mul_apply, hu, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem inv_col {D D' : Matrix ι ι R} {c : ι} (hD : ∀ j k, k ≠ c → D j k = (1 : Matrix ι ι R) j k) (h : D' * D = 1) :
    ∀ j k, k ≠ c → D' j k = (1 : Matrix ι ι R) j k := by
  intro j k hk
  have := congrFun (congrFun h j) k
  rw [Matrix.mul_apply] at this
  rw [← this]
  simp only [hD _ k hk, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Mat

theorem det_row {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] {A : Matrix ι ι R} {c : ι}
    (hA : ∀ j k, j ≠ c → A j k = (1 : Matrix ι ι R) j k) : A.det = A c c := by
  set v : ι → R := Pi.single c 1 with hv
  have hvc : v c = 1 := by simp [hv]
  have hvn : ∀ j, j ≠ c → v j = 0 := fun j hj => by simp [hv, Pi.single_eq_of_ne hj]
  have e : A = 1 + Matrix.replicateCol Unit v * Matrix.replicateRow Unit (A c - v) := by
    ext j k
    have hm : (Matrix.replicateCol Unit v * Matrix.replicateRow Unit (A c - v)) j k = v j * (A c k - v k) := by
      simp [Matrix.mul_apply]
    rw [Matrix.add_apply, hm]
    by_cases hj : j = c
    · subst hj
      by_cases hk : k = j
      · subst hk; rw [hvc, Matrix.one_apply_eq]; ring
      · rw [hvn k hk, Matrix.one_apply_ne (Ne.symm hk), hvc]; ring
    · rw [hA j k hj, hvn j hj, zero_mul, add_zero]
  have h := congrArg Matrix.det e
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hd : (A c - v) ⬝ᵥ v = A c c - 1 := by
    rw [dotProduct, Finset.sum_eq_single c (fun j _ hj => by rw [hvn j hj, mul_zero]) (by simp), hvc, mul_one,
      Pi.sub_apply, hvc]
  rw [hd]; ring

def IdentityOnLastRowsCols {n : ℕ} (i₀ : Fin n) (H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) : Prop :=
  ∀ u ∈ I0 i₀, ∀ v, H u v = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) u v ∧
    H v u = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) v u

theorem isQ_conj {n : ℕ} {i₀ : Fin n} {M H H' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)} {lam : (AE F E)ˣ}
    (hq : IsQ F E i₀ M lam) (hH : H * H' = 1) (h1 : IdentityOnLastRowsCols i₀ H) (h2 : IdentityOnLastRowsCols i₀ H') : IsQ F E i₀ (H * M * H') lam := by
  have mI : Sum.inl i₀ ∈ I0 i₀ := Or.inl rfl
  have mR : Sum.inr i₀ ∈ I0 i₀ := Or.inr rfl
  have hN : H * M * H' = 1 + H * (M - 1) * H' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hH]; abel
  refine ⟨fun a b ha hb => ?_, fun a => ?_, fun b hb => ?_⟩
  · rw [hN, Matrix.add_apply]
    have : (H * (M - 1) * H') a b = 0 := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c ∈ I0 i₀
      · rw [(h1 c hc a).2, Matrix.one_apply_ne (by rintro rfl; exact ha hc), zero_mul, zero_mul]
      · by_cases he : e ∈ I0 i₀
        · rw [(h2 e he b).1, Matrix.one_apply_ne (by rintro rfl; exact hb he), mul_zero]
        · rw [Matrix.sub_apply, hq.off c e hc he, sub_self, mul_zero, zero_mul]
    rw [this, add_zero]
  · rw [mul_col_one (fun v => (h2 _ mI v).2)]
    rw [Matrix.mul_apply]
    simp only [hq.col, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, (h1 _ mI a).2, Matrix.one_apply]
    split_ifs <;> simp_all
  · rw [Matrix.mul_assoc, mul_row_one (fun v => (h1 _ mR v).1), Matrix.mul_apply]
    rw [Finset.sum_eq_single (Sum.inr i₀)]
    · rw [(h2 _ mR b).1, Matrix.one_apply_ne (Ne.symm hb), mul_zero]
    · intro e _ he
      rw [hq.row e he, zero_mul]
    · simp

theorem inFrame_one (d : SD σ) : inFrame d.b (1 : d.G) = 1 := by
  have e : mat2 (1 : d.G) = 1 := rfl
  simp only [inFrame, e, Matrix.mul_one, KWhit.incM_inv_mul]

theorem identityOnLast_embedding {d : SD σ} (L : LD d) (g : L.sd.G) : IdentityOnLastRowsCols L.i₀ (inFrame d.b (L.j g)) := fun u hu v => L.j_out g u hu v

theorem q_conj' {d : SD σ} (L : LD d) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E L.i₀ (inFrame d.b q) lam) (g : L.sd.G) :
    IsQ F E L.i₀ (inFrame d.b (L.j g * q * (L.j g)⁻¹)) lam := by
  have hH : inFrame d.b (L.j g) * inFrame d.b (L.j g)⁻¹ = 1 := by
    rw [← KWhit.inFrame_mul, mul_inv_cancel, inFrame_one]
  rw [KWhit.inFrame_mul, KWhit.inFrame_mul]
  refine isQ_conj hq hH (identityOnLast_embedding L g) ?_
  rw [← map_inv]
  exact identityOnLast_embedding L g⁻¹

end PositivityTheory.SiegelWeilFormula.Avac

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

def ins (z : Fin d.m × Fin L.n × Fin 2 → Af F) : Fin d.m × Fin d.n × Fin 2 → Af F :=
  fun k => if h : ∃ j, L.em j = k.2.1 then z (k.1, h.choose, k.2.2) else 0

def ext (X' : Mx F E d.m L.n) : Mx F E d.m d.n := fun a i => if h : ∃ j, L.em j = i then X' a h.choose else 0

theorem choose_em (j : Fin L.n) (h : ∃ j', L.em j' = L.em j) : h.choose = j := L.inj h.choose_spec

theorem ext_sub (X : Mx F E d.m d.n) (hX : ∀ a, X a L.i₀ = 0) : ext L (X.submatrix id L.em) = X := by
  funext a i
  by_cases h : ∃ j, L.em j = i
  · simp only [ext, dif_pos h, Matrix.submatrix_apply, id, h.choose_spec]
  · have : i = L.i₀ := by
      by_contra hi
      exact h ((L.rng i).1 hi)
    simp only [ext, dif_neg h]
    rw [this, hX]

theorem crd_ext (X' : Mx F E d.m L.n) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (ext L X') k).2 = ins L (fun k' => (L.sd.crd X' k').2) k := by
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [SD.crd, ext, ins, dif_pos h]
  · simp only [SD.crd, ext, ins, dif_neg h, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rfl

theorem continuous_ins : Continuous (ins L (F := F)) := by
  refine continuous_pi fun k => ?_
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [ins, dif_pos h]; exact continuous_apply _
  · simp only [ins, dif_neg h]; exact continuous_const

def prj (z : Fin d.m × Fin d.n × Fin 2 → Af F) : Fin d.m × Fin L.n × Fin 2 → Af F := fun k => z (k.1, L.em k.2.1, k.2.2)

theorem prj_ins (z : Fin d.m × Fin L.n × Fin 2 → Af F) : prj L (ins L z) = z := by
  funext k
  have h : ∃ j, L.em j = L.em k.2.1 := ⟨_, rfl⟩
  simp only [prj, ins, dif_pos h, choose_em L k.2.1 h]

theorem SB_ins {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun z => g (ins L z)) ∈ SB (Fin d.m × Fin L.n × Fin 2 → Af F) := by
  refine ⟨hg.1.comp_continuous (continuous_ins L), ?_⟩
  have hc : IsCompact (prj L '' tsupport g) := hg.2.isCompact.image (continuous_pi fun k => continuous_apply _)
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  refine (tsupport_comp_subset_preimage g (continuous_ins L)).trans fun z hz => ⟨ins L z, hz, prj_ins L z⟩

theorem sum_loc {d : SD σ} (R : RD d) (w : InfinitePlace F) (X : Mx F E d.m d.n) :
    ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 = ∑ i, ∑ a, ‖(((R.fr w)⁻¹).1 *ᵥ fun b => d.cw w X b i) a‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [RD.loc, Matrix.map_apply, norm_star]
  rfl

theorem hζ' {d : SD σ} (R : RD d) : R.ζ = 1 ∨ R.ζ = Complex.I := by
  rcases R.hζ with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

theorem gauss_ext (R : RD d) (R' : RD L.sd) (w : InfinitePlace F) (X' : Mx F E d.m L.n) :
    fP 1 (R.loc w (ext L X')) = fP 1 (R'.loc w X') := by
  suffices key : ∑ a, ∑ i, ‖R'.loc w X' a i‖ ^ 2 = ∑ a, ∑ i, ‖R.loc w (ext L X') a i‖ ^ 2 by
    simp only [fP, gs, key, evX, map_one]
  rw [sum_loc, sum_loc]
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun j => ?_)
  · have h : ¬ ∃ j, L.em j = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
    have : (fun b => d.cw w (ext L X') b i) = 0 := by
      funext b
      simp only [SD.cw, ext, Matrix.map_apply, dif_neg h, map_zero, Pi.zero_apply]
    simp [this]
  · have h : ∃ j', L.em j' = L.em j := ⟨_, rfl⟩
    have e : (fun b => d.cw w (ext L X') b (L.em j)) = fun b => L.sd.cw w X' b j := by
      funext b
      simp only [SD.cw, ext, Matrix.map_apply, dif_pos h, choose_em L j h]
    rw [e]
    exact norm_frame_eq d.ok.hm (d.A.J.map (d.B.emb w).1) (R'.fr w) (R.fr w) R'.ζ R.ζ (R'.sg w) (R.sg w) (hζ' R')
      (hζ' R) (R'.hfr w) (R.hfr w) _

theorem res_vg (R : RD d) (R' : RD L.sd) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) :
    (fun X' => vg R g (ext L X')) = vg R' (fun z => g (ins L z)) := by
  funext X'
  simp only [vg]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => gauss_ext L R R' w X'
  · congr 1
    funext k
    exact crd_ext L X' k

def resL : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m L.n → ℂ) := LinearMap.funLeft ℂ ℂ (ext L)

theorem res_vac (R : RD d) (R' : RD L.sd) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ R.vac) : resL L f ∈ R'.vac := by
  have : R.vac ≤ R'.vac.comap (resL L) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    show resL L (vg R g) ∈ R'.vac
    have e : resL L (vg R g) = vg R' (fun z => g (ins L z)) := res_vg L R R' g
    rw [e]
    exact vg_mem R' (SB_ins L hg)
  exact this hf

theorem vac_res' (hT : TAll) (hF : FockMem) (R : RD d) (R' : RD L.sd) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac := by
  intro Φ hΦ hv
  have h1 : resL L (d.T Φ) ∈ R'.vac := res_vac L R R' hv
  have h2 : resL L (d.T Φ) ∈ L.sd.schM := (hF F E σ L.sd R').1 (vac_le_fock R' h1)
  obtain ⟨Φ', hΦ', e⟩ := (hT.1 F E σ L.sd).2.1 _ h2
  refine ⟨Φ', ⟨hΦ', fun X hX => ?_⟩, e ▸ h1⟩
  rw [e]
  show d.T Φ (ext L (X.submatrix id L.em)) = d.T Φ X
  rw [ext_sub L X hX]

end PositivityTheory.SiegelWeilFormula.Avac

end
end
