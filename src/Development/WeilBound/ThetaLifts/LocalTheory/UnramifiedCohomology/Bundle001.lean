module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle063
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle002
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasAd
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.ExistsSelfDual
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.MemLineStab
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle003
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.Bundle003
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle003
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc
import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle005
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.KAtCompact
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.Bundle002
public import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKG.Loc.Iwa

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.ThK PositivityTheory.ThKH.Iwas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}

theorem mem_iff {ξ : E} (hξ : ξ ≠ 0) (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AE F E)) :
    g ∈ HR (AF F) σ (ξ • Jᵀ) ↔ g ∈ UG (cA σ) (incM F J) := by
  have e : JR (AF F) (ξ • Jᵀ) = inclR (F := F) (AF F) ξ • (incM F J)ᵀ := by
    ext i j; exact map_mul (inclR (F := F) (AF F)) _ _
  have u : IsUnit (inclR (F := F) (AF F) ξ) := (IsUnit.mk0 ξ hξ).map _
  change (g.1.map (cA σ))ᵀ * JR (AF F) (ξ • Jᵀ) * g.1 = JR (AF F) (ξ • Jᵀ) ↔ g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J
  rw [e, Matrix.mul_smul, Matrix.smul_mul, u.smul_left_cancel, ← Matrix.transpose_inj]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

omit [NumberField E] in
theorem compFin_smul (u : Pl F) (a : AF F) (z : AE F E) : compFin F E u (a • z) = evFin F u a • compFin F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evFin F u) a b)
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

omit [NumberField E] in
theorem compInf_smul (u : InfinitePlace F) (a : AF F) (z : AE F E) : compInf F E u (a • z) = evInf F u a • compInf F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evInf F u) a b)
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem at_emb {J : Matrix (Fin n) (Fin n) E} (z : GLoc σ J v) : At (evFin F v) ((matHom _ σ J (emb σ J v z)).1 - 1) := by
  intro a ha
  ext i j
  have one : ∀ {S : Type} [CommRing S] (f : AE F E →+* S), f ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j) =
      (1 : Matrix (Fin n) (Fin n) S) i j := fun f => congrFun (congrFun (Matrix.map_one f (map_zero _) (map_one _)) i) j
  change a • ((matHom _ σ J (emb σ J v z)).1 i j - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = 0
  refine Supp.adTens_ext (fun w => ?_) fun u => ?_
  · have := congrArg (fun x => (matHom _ σ J x).1 i j) (projArch_emb σ J w v z)
    rw [compInf_smul, map_sub, one, map_zero]
    exact smul_eq_zero_of_right _ (sub_eq_zero.2 this)
  · rw [compFin_smul, map_zero]
    by_cases h : u = v
    · subst h; rw [ha, zero_smul]
    · have := congrArg (fun x => (matHom _ σ J x).1 i j) (proj_emb_ne σ J h z)
      rw [map_sub, one]
      exact smul_eq_zero_of_right _ (sub_eq_zero.2 this)

theorem mem_latW_iff' (W : Spc F E n) (y : Fin n → AE F E) :
    y ∈ latW W v ↔ At (evFin F v) y ∧ (fun i => compFin F E v (y i)) ∈ latLoc F W.L v := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hi, x, hx, rfl⟩ := hz
      refine ⟨fun u hu => funext fun i => ?_, ?_⟩
      · change u • a • inclR (F := F) (AF F) (x i) = 0
        rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      · convert tmul_mem_latLoc hi hx using 2 with i
        rw [compFin_smul]
        change evFin F v a • (evFin F v 1 ⊗ₜ[F] x i) = _
        rw [map_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | zero => exact ⟨at_zero, by simp only [Pi.zero_apply, map_zero]; exact zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨at_add ha.1 hb.1, by simp only [Pi.add_apply, map_add (f := _)]; exact add_mem ha.2 hb.2⟩
    | neg a _ ha => exact ⟨by simpa using at_sub at_zero ha.1, by simp only [Pi.neg_apply, map_neg]; exact neg_mem ha.2⟩
  · rintro ⟨h1, h2⟩
    have key : ∀ z ∈ latLoc F W.L v, (fun i => sgE E v (z i)) ∈ latW W v := fun z hz => by
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨sg v a, at_sg a, by rw [ev_sg]; exact ha, x, hx, funext fun i => ?_⟩
        change sg v a ⊗ₜ[F] x i = (sg v a * 1) ⊗ₜ[F] x i
        rw [mul_one]
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add a b _ _ ha hb => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem ha hb
      | neg a _ ha => simp only [Pi.neg_apply, map_neg]; exact neg_mem ha
    convert key _ h2 using 1
    funext i
    refine sub_eq_zero.1 (eq_zero_of_at (v := v) (at_sub (fun u hu => congrFun (h1 u hu) i) (at_sgE _)) ?_)
    rw [map_sub, comp_sgE, sub_self]

theorem stab_latW {Y : Spc F E n} {k : UA σ Y.J} (hk : k ∈ UAt σ Y (evFin F v)) {κ : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (e : (mat k).map (compFin F E v) = κ) (h : ∀ z ∈ latLoc F Y.L v, κ *ᵥ z ∈ latLoc F Y.L v) :
    ∀ y ∈ latW Y v, mat k *ᵥ y ∈ latW Y v := fun y hy => by
  obtain ⟨h1, h2⟩ := (mem_latW_iff' Y y).1 hy
  refine (mem_latW_iff' Y _).2 ⟨at_mulVec_right _ h1, ?_⟩
  convert h _ h2 using 1
  funext i
  rw [← e]
  exact RingHom.map_mulVec (compFin F E v) _ y i

def bk {ξ : E} (hξ : ξ ≠ 0) (J : Matrix (Fin n) (Fin n) E) : GAd σ (ξ • Jᵀ) →* UA σ J where
  toFun z := ⟨matHom _ σ _ z, (mem_iff hξ _ _).1 z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mat_bk {ξ : E} (hξ : ξ ≠ 0) (J : Matrix (Fin n) (Fin n) E) (z : GAd σ (ξ • Jᵀ)) :
    mat (bk hξ J z) = (matHom _ σ _ z).1 := rfl

theorem bk_surj {ξ : E} (hξ : ξ ≠ 0) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) : ∃ z, bk (σ := σ) hξ J z = g :=
  ⟨⟨g.1, (mem_iff hξ _ _).2 g.2⟩, rfl⟩

theorem iwaLoc {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    {x : Fin n → E} (hx : x ≠ 0) (h0 : form σ Y.J x x = 0) (v : Pl F) {g : UA σ Y.J} (hg : g ∈ UAt σ Y (evFin F v)) :
    ∃ p ∈ UAt σ Y (evFin F v), ∃ k ∈ KAt σ Y v, ∃ t : (AE F E)ˣ,
      mat p *ᵥ GlobalTheory.ThK.incV F x = t.1 • GlobalTheory.ThK.incV F x ∧ g = p * k := by
  obtain ⟨ξ, hξ, hJ, hL⟩ := exists_selfDual hB hY v
  haveI := hB.unram
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance
  haveI : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨g', rfl⟩ := bk_surj hξ Y.J g
  obtain ⟨q, k, ⟨t, ht⟩, hk, e⟩ := core hB.cm hθ hJ Y.L (unramAt hB v)
    ((isEmpty_or_nonempty _).symm.imp_right (inert_of_local F E σ B hB v)) hL hx (by
      have := hE_smul (σ := σ) ξ Y.J x x
      rw [h0, mul_zero] at this
      rw [← this]
      simp only [hE, Formalism.UG.hform, Matrix.vecMul, dotProduct, Finset.sum_mul]
      exact Finset.sum_comm) (proj σ _ v g')
  have cmp : ∀ z : GLoc σ (ξ • Y.Jᵀ) v, (mat (bk hξ Y.J (emb σ _ v z))).map (compFin F E v) = (matHom _ σ _ z).1 := fun z => by
    rw [mat_bk]
    exact congrArg (fun x => (matHom _ σ _ x).1) (proj_emb_self σ _ v z)
  have hat : ∀ z : GLoc σ (ξ • Y.Jᵀ) v, bk hξ Y.J (emb σ _ v z) ∈ UAt σ Y (evFin F v) := fun z => by
    change At _ (mat _ - 1)
    rw [mat_bk]
    exact at_emb z
  refine ⟨_, hat q, _, ⟨hat k, fun y hy => ⟨stab_latW (hat k) (cmp k) (fun z hz => (hk z).1 hz) y hy, ?_⟩⟩, t,
    by rw [mat_bk]; exact ht, ?_⟩
  · rw [← map_inv, ← map_inv]
    have hk' : k⁻¹ ∈ stabLoc σ _ Y.L v := inv_mem hk
    exact stab_latW (hat k⁻¹) (cmp k⁻¹) (fun z hz => (hk' z).1 hz) y hy
  · rw [← map_mul, ← map_mul, ← e]
    have c1 := cmp (proj σ _ v g')
    have a1 := at_sub hg (hat (proj σ _ v g'))
    have c2 : (mat (bk hξ Y.J g')).map (compFin F E v) = (matHom _ σ _ (proj σ _ v g')).1 := by rw [mat_bk]; rfl
    rw [← c2] at c1
    generalize bk hξ Y.J (emb σ _ v (proj σ _ v g')) = a at c1 a1
    generalize bk hξ Y.J g' = b at c1 a1
    rw [sub_sub_sub_cancel_right] at a1
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => sub_eq_zero.1 (eq_zero_of_at (v := v) (fun u hu => ?_) ?_)))
    · exact congrFun (congrFun (a1 u hu) i) j
    · rw [map_sub, sub_eq_zero]
      exact (congrFun (congrFun c1 i) j).symm

end PositivityTheory.ThKG.Loc.Iwa

end
end

section

noncomputable section

namespace PositivityTheory.ThKG.Loc.FL

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Fin PositivityTheory.ThKCT
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}
  {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

attribute [local instance] PositivityTheory.ThK.kc_ring PositivityTheory.ThK.adele_t2Space PositivityTheory.ThK.kc_smul

theorem tate' (hI : IdeleFub) (hJ : IdealId0) (hS : StabEx) {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁}
    {H : Plane E n n₁} {H' : Plane E d d₁} {e u ei ev} (hc : Cfg B M M₁ H H' e u) (h : IsEvLoc M M₁ e ei ev) (v : Pl F)
    {K : Subgroup (UA σ X.J)} (m : LocMeas K) (hm : m.Is) {ν : Chr F E} (hν : Continuous ν) {z : ℕ} (hz : 2 ≤ z)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) :
    (Set.range fun l : idAt E (evFin F v) => ev v (rv B M v (idem F v • u l.1) φ)).Finite ∧
      IsLocallyConstant (fun l : idAt E (evFin F v) => ev v (rv B M v (idem F v • u l.1) φ)) ∧
      @IntegrableOn _ _ (borel _) _ _ (fun l : idAt E (evFin F v) => wt ν z l.1)
        {l | ev v (rv B M v (idem F v • u l.1) φ) ≠ 0} (m.xf v) := by
  letI : MeasurableSpace (idAt E (evFin F v)) := borel _
  haveI : BorelSpace (idAt E (evFin F v)) := ⟨rfl⟩
  haveI := (hm.xf v).1
  obtain ⟨V₀, V₁, c, hu, -, -, hinv, hcomp⟩ := dirs hc
  obtain ⟨r, s, hX⟩ := hc.herm
  obtain ⟨r', s', hW⟩ := hc.skew
  obtain ⟨i, j, hH⟩ := hc.hH
  obtain ⟨i', j', hH'⟩ := hc.hH'
  obtain ⟨𝔞, h𝔞, hin⟩ := hJ F E σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i j i' j' hc.base hX hW hH hH' u
    (hc.ev.imp And.right And.right)
  obtain ⟨-, -, μ, -, -, -, hμ⟩ := hS F E σ B n X r s hc.base hX
  obtain ⟨πi, π, κ, -, hπ, hF⟩ := hI F E σ B n X K m μ hc.base hm hμ 𝔞 z h𝔞 hz
  have hint := ((hF 1 ∅ ∅ continuous_const (Finset.Subset.refl _) (fun w _ x _ => map_one Circle.toUnits)
    (fun w hw => absurd hw (Finset.notMem_empty _))).1 v (Finset.notMem_empty v)).2
  obtain ⟨N, hN, hfix⟩ := exists_level hc.base hX hW M v hφ
  obtain ⟨C, hC, hCΓ⟩ := lat_compact hX hW M v
  let g : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → Fl F v n₁ d₁ := fun w => ev v (schr (psiAt B.ψ v) w φ)
  have hg : IsLocallyConstant g := (schr_lc (psi_lc hc.base v) fun w => rv_sb hc.base M v w hφ).comp (ev v)
  have e1 : ∀ l : (AE F E)ˣ, locCo M.co v (idem F v • u l) = locCo M.co v (c l.1 • V₀) := fun l => by
    rw [locCo_smul, evFin_idem, one_smul, hu]
  have hG : IsLocallyConstant fun l : idAt E (evFin F v) => ev v (rv B M v (idem F v • u l.1) φ) := by
    simp only [rv, e1]
    exact hg.comp_continuous ((cont_loc M v c V₀).comp (Units.continuous_val.comp continuous_subtype_val))
  have hk : ∀ l : (AE F E)ˣ, ev v (rv B M v (idem F v • u l) φ) ≠ 0 → (N : AF F) • idem F v • u l ∈ latAtV X W v := fun l hl => by
    have e2 : idem F v • u l = (idem F v • c l.1) • V₀ := by rw [hu, smul_assoc]
    rw [e2] at hl ⊢
    exact key hc h hinv (hcomp v) hφ N (fun t ht => hfix _ ht) _ (e2 ▸ PositivityTheory.ThKG.Loc.Cone.Fin.at_idem v _) hl
  have hN' : (N : Fv F v) ≠ 0 := by
    haveI : CharZero (Fv F v) := algebraRat.charZero _
    exact Nat.cast_ne_zero.2 hN
  refine ⟨?_, hG, ?_⟩
  · haveI := isCompact_iff_compactSpace.1 hC
    have hf := (hg.comp_continuous ((continuous_subtype_val (p := (· ∈ C))).const_smul (N : Fv F v)⁻¹)).range_finite
    refine (hf.insert 0).subset ?_
    rintro _ ⟨l, rfl⟩
    by_cases h0 : ev v (rv B M v (idem F v • u l.1) φ) = 0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨_, hCΓ _ (hk _ h0)⟩, ?_⟩
      change g ((N : Fv F v)⁻¹ • locCo M.co v ((N : AF F) • idem F v • u l.1)) = _
      rw [locCo_smul M v (N : AF F), map_natCast, inv_smul_smul₀ hN']
  · have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN
    let lN : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (N : E) hNE)
    let l₀ := π v lN
    have hl₀ : (l₀.1 : AE F E) = idem F v • (N : AE F E) + (1 - idem F v) • (1 : AE F E) := by
      have := (hπ lN).2 v
      rw [IsPart, show (lN : AE F E) = (N : AE F E) from map_natCast (inclR (F := F) (AF F)) N] at this
      exact this
    have e3 : ∀ l : idAt E (evFin F v), idem F v • u (l₀ * l).1 = (N : AF F) • idem F v • u l.1 := fun l => by
      rw [hu, hu, ← smul_assoc, ← smul_assoc, ← smul_assoc]
      congr 1
      have q : algebraMap (AF F) (AE F E) (idem F v) * algebraMap (AF F) (AE F E) (idem F v) =
          algebraMap (AF F) (AE F E) (idem F v) := by rw [← map_mul, idem_sq]
      rw [Subgroup.coe_mul, Units.val_mul, map_mul, hl₀, map_add (f := _), map_smul, map_smul, map_natCast, map_one]
      simp only [Algebra.smul_def, smul_eq_mul, map_mul, map_sub, map_one, map_natCast, Algebra.algebraMap_self, RingHom.id_apply]
      linear_combination ((N : AE F E) * c l.1.1 - c l.1.1) * q
    have h0 : (0 : ℝ) < absE F E l₀.1 := by
      refine lt_of_le_of_ne NNReal.zero_le_coe fun e => ?_
      have : absE F E l₀.1 * absE F E l₀.1⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [show absE F E l₀.1 = 0 from NNReal.coe_eq_zero.1 e.symm, zero_mul] at this
      exact zero_ne_one this
    refine Integrable.mono' (((hint.comp_mul_left l₀).norm.const_mul (((absE F E l₀.1 : ℝ) ^ z)⁻¹)).integrableOn)
      ((cont_wt hν z).comp continuous_subtype_val).aestronglyMeasurable
      (ae_restrict_of_forall_mem (hG.isClosed_fiber 0).measurableSet.compl fun l hl => ?_)
    have := (hin v (l₀ * l).1).1 (e3 l ▸ hk _ hl)
    rw [if_pos this, one_mul, norm_wt, norm_wt, Subgroup.coe_mul, map_mul, NNReal.coe_mul, mul_pow,
      inv_mul_cancel_left₀ (pow_pos h0 z).ne']

theorem int_lin {α Y : Type} [MeasurableSpace α] (μ : Measure α) (G : α → Y → ℂ) (w : α → ℂ) (hf : (Set.range G).Finite)
    (hm : ∀ g, MeasurableSet {a | G a = g}) (D : Set α) (hD : ∀ a ∉ D, G a = 0) (hw : IntegrableOn w D μ)
    (l : (Y → ℂ) →ₗ[ℂ] ℂ) : l (fun y => ∫ a, G a y * w a ∂μ) = ∫ a, l (G a) * w a ∂μ := by
  let Φ : (Y → ℂ) → Option Y → ℂ := fun g o => o.elim (l g) g
  have inj : Function.Injective Φ := fun g g' e => funext fun y => congrFun e (some y)
  have := (int_fin μ (fun a => Φ (G a)) w ((hf.image Φ).subset (by rintro _ ⟨a, rfl⟩; exact ⟨_, ⟨a, rfl⟩, rfl⟩))
    (fun g => by
      by_cases h : ∃ g', Φ g' = g
      · obtain ⟨g', rfl⟩ := h
        simpa only [inj.eq_iff] using hm g'
      · have he : {a | Φ (G a) = g} = ∅ :=
          Set.eq_empty_of_forall_notMem fun a ha => h ⟨G a, ha⟩
        rw [he]
        exact MeasurableSet.empty) D
    (fun a ha => by rw [hD a ha]; funext o; cases o <;> simp [Φ]) hw
    (LinearMap.ker (LinearMap.proj none - l ∘ₗ LinearMap.funLeft ℂ ℂ some)) fun a => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]; rfl).2
  exact (sub_eq_zero.1 this).symm

theorem ev_loc {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {e ei ev} (h : IsEvLoc M M₁ e ei ev) {v : Pl F} {S S₁} {c : ℂ} (he : ∀ Φ ∈ schA F _, e (S Φ) = c • S₁ (e Φ))
    {φ φ' : Fl F v n d} (hφ : φ ∈ SB _) (hφ' : φ' ∈ SB _) (hS : Acts (evFin F v) S φ φ') {ψ}
    (hS₁ : Acts (evFin F v) S₁ (ev v φ) ψ) : ev v φ' = c • ψ := by
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h.ne (ContinuousLinearMap.ext hn)
  have gen : ∀ {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}, M.IsGood B.ψ → ∀ a : Fl F v n d, a ∈ SB _ →
      (∀ u, Function.update M.vac v a u ∈ SB _) ∧ (∀ᶠ u in cofinite, Function.update M.vac v a u = M.vac u) ∧
      ∀ᶠ u in cofinite, Function.update M.vac v a u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1 := by
    intro n d X W M hM a ha
    have cf : ∀ᶠ u in cofinite, Function.update M.vac v a u = M.vac u := by
      filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with u hu using Function.update_of_ne hu _ _
    refine ⟨fun u => ?_, cf, by filter_upwards [cf, hM.std] with u a b using a.trans b⟩
    by_cases e : u = v
    · subst e; rwa [Function.update_self]
    · rw [Function.update_of_ne e]; exact (hM.vac u).1
  have up : ∀ a : Fl F v n d, (fun u => ev u (Function.update M.vac v a u)) = Function.update M₁.vac v (ev v a) := fun a =>
    funext fun u => by
      by_cases e : u = v
      · subst e; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne e, Function.update_of_ne e, (h.vac u).1]
  have hev : ev v φ ∈ SB _ := (h.vac v).2 ▸ Submodule.mem_map_of_mem hφ
  obtain ⟨s1, c1, t1⟩ := gen hM φ hφ
  obtain ⟨s2, c2, -⟩ := gen hM φ' hφ'
  obtain ⟨s3, -, t3⟩ := gen hM₁ _ hev
  have h1 := (PositivityTheory.ThKF.pureAct F _ v S f _ s1 t1).2.2 φ' (by rwa [Function.update_self])
  obtain ⟨-, lin, h3⟩ := PositivityTheory.ThKF.pureAct F _ v S₁ (ei f) _ s3 t3
  have h3' := h3 ψ (by rwa [Function.update_self])
  have l0 := lin 0 0 1
  have l1 := lin 0 ψ c
  simp only [Function.update_idem, smul_zero, add_zero, one_smul, zero_add, left_eq_add] at l0 l1 h3'
  have h2 := he _ (GlobalTheory.TensUniq.pure_mem_schA f _ s1 t1)
  rw [h1, Function.update_idem, h.pure f _ s2 c2, h.pure f _ s1 c1, up, up, h3'] at h2
  rw [l0, zero_add] at l1
  exact pure_cancel (fun u => (hM₁.vac u).2.1) hM₁.std v hf (h2.trans l1.symm)

theorem loc_form {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
    (v : Pl F) (x u : V) :
    (locCo co v x).1 ⬝ᵥ (locCo co v u).2 - (locCo co v u).1 ⬝ᵥ (locCo co v x).2 = evFin F v (Bf x u) := by
  rw [co.form]

  simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]

theorem rv_add (B : Base F E) (M : Model σ X W) (v : Pl F) {x : Fin d → E} (hx : form σ W.J x x = 0) (p q : Fin n → AE F E)
    (φ : Fl F v n d) : rv B M v (Matrix.vecMulVec (p + q) (incV F x)) φ =
      rv B M v (Matrix.vecMulVec p (incV F x)) (rv B M v (Matrix.vecMulVec q (incV F x)) φ) := by
  have h0 : hTens (cA σ) (incM F X.J) (incM F W.J) (Matrix.vecMulVec p (incV F x)) (Matrix.vecMulVec q (incV F x)) = 0 := by
    have e : ∑ j, ∑ l, incV F x j * incM F W.J j l * cA σ (incV F x l) = 0 := by
      have := congrArg (inclR (F := F) (AF F)) hx
      rw [map_zero] at this
      rw [← this]

      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, mul_assoc]
      rfl
    calc _ = ∑ i, ∑ k, p i * incM F X.J i k * cA σ (q k) * ∑ j, ∑ l, incV F x j * incM F W.J j l * cA σ (incV F x l) := by
          simp only [hTens, Matrix.vecMulVec_apply, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      _ = 0 := by simp [e]
  rw [rv, rv, rv, schr_mul, loc_form, symp, h0, Matrix.add_vecMulVec, map_add (f := _)]
  simp

theorem span_soLoc (hL : LinEx) {B : Base F E} (hB : B.IsGood σ) {r s r' s'} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (M : Model σ X W) {v : Pl F} (t : E →ₐ[F] Fv F v) {φ} (h : φ ∈ Submodule.span ℂ (M.SoLoc B.ψ t)) : φ ∈ M.SoLoc B.ψ t := by
  obtain ⟨⟨ι, hι⟩, -⟩ := hL F E σ B n d X W M r s r' s' hB hX hW v t
  refine ⟨(Submodule.span_le.2 fun χ (hχ : χ ∈ M.SoLoc B.ψ t) => hχ.1 : _ ≤ SB _) h, ι, hι, fun Y hY => ?_⟩
  have : Submodule.span ℂ (M.SoLoc B.ψ t) ≤ LinearMap.ker (LinearMap.proj Y ∘ₗ ι) := Submodule.span_le.2 fun χ hχ =>
    PositivityTheory.KCo.full_of_soLoc M hB.cm hB.std (Fr.det_ne (.inl hX)) (Fr.det_ne (.inr hW)) hι hχ Y hY
  exact this h

end PositivityTheory.ThKG.Loc.FL

end
end
