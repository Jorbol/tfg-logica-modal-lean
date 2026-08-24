import Mathlib.Tactic
import Mathlib.Order.Zorn

/-!
# Lógica modal K en Lean 4: corrección y completitud

Formalización del sistema modal K y de su adecuación respecto a la semántica
de Kripke. El fichero se organiza en seis secciones, que el capítulo 4 de la
memoria recorre en este mismo orden:

1. Sintaxis: las fórmulas modales como tipo inductivo.
2. Tautologías clásicas: el evaluador `cplEval` y el esquema (CPL).
3. El sistema axiomático K: la demostrabilidad `Provable` y las reglas RM y RE.
4. Semántica de Kripke: marcos, modelos, satisfacción y validez.
5. Corrección: el teorema `soundness` y la consistencia de K.
6. Completitud: deducción con hipótesis, conjuntos maximales consistentes,
   lema de Lindenbaum (vía Zorn), modelo canónico y el teorema `completeness`.

Convenciones. Las conectivas del lenguaje objeto usan símbolos propios
(`⟶`, `□`, `∼`, `⋏`, `⋎`, `⟷`, `◇`), distintos de los de Lean (`→`, `¬`,
`∧`, `∨`, `↔`). Las hipótesis se nombran `h` seguido de lo que afirman (`hφ`,
`hsub`, `hbox`) y las hipótesis de inducción, `ih`; un guion bajo inicial
(`_hφ`) marca una hipótesis que no se usa.
-/


/-! ## 1. Sintaxis -/

/-- Fórmulas modales sobre un tipo `VP` de variables proposicionales. El
lenguaje primitivo tiene cuatro constructores: variables, `⊥`, implicación y
necesidad (`□`); las demás conectivas se definen a partir de ellos. -/
inductive ModalFormula (VP : Type) where
  | atom : VP → ModalFormula VP                                 -- variable
  | bot  : ModalFormula VP                                      -- ⊥
  | imp  : ModalFormula VP → ModalFormula VP → ModalFormula VP  -- implicación
  | box  : ModalFormula VP → ModalFormula VP                    -- □

local infixr:60 " ⟶ " => ModalFormula.imp
local prefix:70 "□"    => ModalFormula.box

-- A partir de aquí, `VP` es un argumento implícito de todas las definiciones
variable {VP : Type}

/-- Verdad: `⊤ := ⊥ ⟶ ⊥`. -/
def ModalFormula.top : ModalFormula VP :=
  ModalFormula.bot ⟶ ModalFormula.bot

/-- Negación: `∼φ := φ ⟶ ⊥`. -/
def ModalFormula.neg (φ : ModalFormula VP) : ModalFormula VP :=
  φ ⟶ ModalFormula.bot
local prefix:75 "∼" => ModalFormula.neg

/-- Disyunción: `φ ⋎ ψ := ∼φ ⟶ ψ`. -/
def ModalFormula.or (φ ψ : ModalFormula VP) : ModalFormula VP :=
  (∼φ) ⟶ ψ
local infixl:65 " ⋎ " => ModalFormula.or

/-- Conjunción: `φ ⋏ ψ := ∼(φ ⟶ ∼ψ)`. -/
def ModalFormula.and (φ ψ : ModalFormula VP) : ModalFormula VP :=
  ∼(φ ⟶ (∼ψ))
local infixl:67 " ⋏ " => ModalFormula.and

/-- Bicondicional: `φ ⟷ ψ := (φ ⟶ ψ) ⋏ (ψ ⟶ φ)`. -/
def ModalFormula.iff (φ ψ : ModalFormula VP) : ModalFormula VP :=
  (φ ⟶ ψ) ⋏ (ψ ⟶ φ)
local infixl:55 " ⟷ " => ModalFormula.iff

/-- Posibilidad: `◇φ := ∼□∼φ`. -/
def ModalFormula.dia (φ : ModalFormula VP) : ModalFormula VP :=
  ∼(□(∼φ))
local prefix:70 "◇" => ModalFormula.dia


/-! ## 2. Tautologías clásicas -/

/-- Evaluación clásica de una fórmula dadas una valoración `v_atom` de las
variables y una valoración `v_box` de las fórmulas encajonadas. La caja se
trata como un átomo opaco: para evaluar `□φ` no se mira dentro de `φ`. -/
def cplEval (v_atom : VP → Prop) (v_box : ModalFormula VP → Prop) :
    ModalFormula VP → Prop
  | ModalFormula.atom x  => v_atom x
  | ModalFormula.bot     => False
  | ModalFormula.imp φ ψ => cplEval v_atom v_box φ → cplEval v_atom v_box ψ
  | ModalFormula.box φ   => v_box φ    -- la caja es un átomo opaco

/-- Una fórmula es una tautología clásica si su evaluación es verdadera para
cualesquiera valoraciones de las variables y de las fórmulas encajonadas. -/
def IsCPLTautology (φ : ModalFormula VP) : Prop :=
  ∀ (v_atom : VP → Prop) (v_box : ModalFormula VP → Prop),
    cplEval v_atom v_box φ

/-- Identidad: `φ ⟶ φ`. Como la demostración no inspecciona `φ`, vale en
particular para `φ := □ψ`; en cambio, `□φ ⟶ φ` no es tautología clásica. -/
theorem taut_id (φ : ModalFormula VP) : IsCPLTautology (φ ⟶ φ) := by
  intro v_atom v_box hφ
  -- cplEval traduce ⟶ en la implicación → de Lean: la hipótesis es el objetivo
  exact hφ

/-- Debilitamiento (axioma A1 de Hilbert): `ψ ⟶ (φ ⟶ ψ)`. -/
theorem taut_weaken (ψ φ : ModalFormula VP) :
    IsCPLTautology (ψ ⟶ (φ ⟶ ψ)) := by
  intro v_atom v_box hψ _hφ
  exact hψ

/-- Distribución de la implicación (axioma A2 de Hilbert):
`(φ ⟶ (ψ ⟶ χ)) ⟶ ((φ ⟶ ψ) ⟶ (φ ⟶ χ))`. -/
theorem taut_dist (φ ψ χ : ModalFormula VP) :
    IsCPLTautology ((φ ⟶ (ψ ⟶ χ)) ⟶ ((φ ⟶ ψ) ⟶ (φ ⟶ χ))) := by
  intro v_atom v_box hφψχ hφψ hφ
  -- De φ salen ψ ⟶ χ (por hφψχ) y ψ (por hφψ); juntas dan χ
  exact hφψχ hφ (hφψ hφ)

/-- Eliminación de la doble negación: `∼∼φ ⟶ φ`. Es un principio clásico,
no demostrable intuicionistamente. -/
theorem taut_dne (φ : ModalFormula VP) : IsCPLTautology (∼∼φ ⟶ φ) := by
  intro v_atom v_box hnn
  -- hnn dice que no se da ∼φ; por reducción al absurdo se obtiene φ
  by_contra hn
  exact hnn hn

/-- Explosión (ex falso quodlibet): `∼φ ⟶ (φ ⟶ ψ)`. -/
theorem taut_exfalso (φ ψ : ModalFormula VP) :
    IsCPLTautology (∼φ ⟶ (φ ⟶ ψ)) := by
  intro v_atom v_box hnφ hφ
  -- hnφ hφ es una contradicción (un término de False): de ella sale todo
  exact False.elim (hnφ hφ)

/-- De `φ ⟷ ψ` se extrae `φ ⟶ ψ`. -/
theorem taut_iff_mp (φ ψ : ModalFormula VP) :
    IsCPLTautology ((φ ⟷ ψ) ⟶ (φ ⟶ ψ)) := by
  intro v_atom v_box hiff
  -- Por reducción al absurdo: suponemos que φ_eval → ψ_eval falla
  by_contra hnimp
  -- hiff niega (φ_eval → ψ_eval) → ¬(ψ_eval → φ_eval); basta probar eso
  apply hiff
  intro himp
  -- himp : φ_eval → ψ_eval contradice hnimp
  contradiction

/-- De `φ ⟷ ψ` se extrae `ψ ⟶ φ`. -/
theorem taut_iff_mpr (φ ψ : ModalFormula VP) :
    IsCPLTautology ((φ ⟷ ψ) ⟶ (ψ ⟶ φ)) := by
  intro v_atom v_box hiff
  by_contra hnimp
  -- Ahora hnimp : ¬(ψ_eval → φ_eval) es exactamente lo que hiff pide
  apply hiff
  intro _
  exact hnimp

/-- De `φ ⟶ ψ` y `ψ ⟶ φ` se reconstruye `φ ⟷ ψ`. -/
theorem taut_iff_intro (φ ψ : ModalFormula VP) :
    IsCPLTautology ((φ ⟶ ψ) ⟶ (ψ ⟶ φ) ⟶ (φ ⟷ ψ)) := by
  intro v_atom v_box hφψ hψφ hcontra
  -- hcontra : (φ_eval → ψ_eval) → ¬(ψ_eval → φ_eval); la aplicamos a hφψ
  have hnψφ := hcontra hφψ
  -- ...y el resultado contradice hψφ
  exact hnψφ hψφ


/-! ## 3. El sistema axiomático K -/

/-- Demostrabilidad en el sistema K: `Provable φ` formaliza `⊢ φ`. Los
constructores `cpl` y `k` son los axiomas; `mp` y `nec`, las reglas. -/
inductive Provable : ModalFormula VP → Prop where
  -- (CPL) toda tautología clásica es un teorema
  | cpl (φ : ModalFormula VP) (h : IsCPLTautology φ) : Provable φ
  -- (MP) de ⊢ φ ⟶ ψ y ⊢ φ se obtiene ⊢ ψ
  | mp  {φ ψ : ModalFormula VP} (hφψ : Provable (φ ⟶ ψ)) (hφ : Provable φ) :
        Provable ψ
  -- (K) distribución de □ sobre ⟶
  | k   (φ ψ : ModalFormula VP) : Provable (□(φ ⟶ ψ) ⟶ (□φ ⟶ □ψ))
  -- (N) necesitación: de ⊢ φ se obtiene ⊢ □φ
  | nec {φ : ModalFormula VP} (h : Provable φ) : Provable (□φ)

/-- `⊢ (φ ⟷ ψ) ⟶ (φ ⟶ ψ)`: la tautología `taut_iff_mp` como teorema de K. -/
theorem provable_iff_mp (φ ψ : ModalFormula VP) :
    Provable ((φ ⟷ ψ) ⟶ (φ ⟶ ψ)) :=
  Provable.cpl _ (taut_iff_mp φ ψ)

/-- `⊢ (φ ⟷ ψ) ⟶ (ψ ⟶ φ)`: la tautología `taut_iff_mpr` como teorema de K. -/
theorem provable_iff_mpr (φ ψ : ModalFormula VP) :
    Provable ((φ ⟷ ψ) ⟶ (ψ ⟶ φ)) :=
  Provable.cpl _ (taut_iff_mpr φ ψ)

/-- `⊢ (φ ⟶ ψ) ⟶ (ψ ⟶ φ) ⟶ (φ ⟷ ψ)`: `taut_iff_intro` como teorema de K. -/
theorem provable_iff_intro (φ ψ : ModalFormula VP) :
    Provable ((φ ⟶ ψ) ⟶ (ψ ⟶ φ) ⟶ (φ ⟷ ψ)) :=
  Provable.cpl _ (taut_iff_intro φ ψ)

/-- Regla de monotonía (RM): de `⊢ φ ⟶ ψ` se obtiene `⊢ □φ ⟶ □ψ`. -/
theorem provable_rm {φ ψ : ModalFormula VP} (hφψ : Provable (φ ⟶ ψ)) :
    Provable (□φ ⟶ □ψ) := by
  -- Necesitación sobre la hipótesis
  have hnec : Provable (□(φ ⟶ ψ)) := Provable.nec hφψ
  -- Axioma K: la caja distribuye sobre la implicación
  have hK : Provable (□(φ ⟶ ψ) ⟶ (□φ ⟶ □ψ)) := Provable.k φ ψ
  -- Modus ponens
  exact Provable.mp hK hnec

/-- Regla de equivalencia (RE): de `⊢ φ ⟷ ψ` se obtiene `⊢ □φ ⟷ □ψ`. -/
theorem provable_re {φ ψ : ModalFormula VP} (h : Provable (φ ⟷ ψ)) :
    Provable (□φ ⟷ □ψ) := by
  -- Extraemos ⊢ φ ⟶ ψ y aplicamos RM
  have hmp : Provable ((φ ⟷ ψ) ⟶ (φ ⟶ ψ)) := provable_iff_mp φ ψ
  have hφψ : Provable (φ ⟶ ψ) := Provable.mp hmp h
  have hboxφψ : Provable (□φ ⟶ □ψ) := provable_rm hφψ
  -- Extraemos ⊢ ψ ⟶ φ y aplicamos RM
  have hmpr : Provable ((φ ⟷ ψ) ⟶ (ψ ⟶ φ)) := provable_iff_mpr φ ψ
  have hψφ : Provable (ψ ⟶ φ) := Provable.mp hmpr h
  have hboxψφ : Provable (□ψ ⟶ □φ) := provable_rm hψφ
  -- Reensamblamos el bicondicional con dos modus ponens
  have hintro : Provable ((□φ ⟶ □ψ) ⟶ (□ψ ⟶ □φ) ⟶ (□φ ⟷ □ψ)) :=
    provable_iff_intro (□φ) (□ψ)
  have hstep : Provable ((□ψ ⟶ □φ) ⟶ (□φ ⟷ □ψ)) := Provable.mp hintro hboxφψ
  exact Provable.mp hstep hboxψφ


/-! ## 4. Semántica de Kripke -/

/-- Un marco de Kripke: un tipo de mundos y una relación de accesibilidad
entre ellos. `R w v` se lee "desde el mundo `w` es accesible el mundo `v`". -/
structure KripkeFrame where
  World : Type
  R : World → World → Prop

/-- Un modelo de Kripke: un marco junto con una valoración `V` que dice, para
cada mundo, qué variables proposicionales son verdaderas en él. -/
structure KripkeModel (VP : Type) extends KripkeFrame where
  V : World → VP → Prop

/-- Satisfacción: `Satisfies M w φ` formaliza `M, w ⊨ φ`. Se define por
recursión sobre la fórmula; en la cláusula de `□` la caja deja de ser opaca
y su significado viene dado por la relación `R`. -/
def Satisfies (M : KripkeModel VP) (w : M.World) : ModalFormula VP → Prop
  | ModalFormula.atom x  => M.V w x
  | ModalFormula.bot     => False
  | ModalFormula.imp φ ψ => Satisfies M w φ → Satisfies M w ψ
  | ModalFormula.box φ   => ∀ v : M.World, M.R w v → Satisfies M v φ

/-- `∼p` es verdadera en `w` exactamente cuando `p` no lo es. -/
theorem satisfies_neg (M : KripkeModel VP) (w : M.World) (p : ModalFormula VP) :
    Satisfies M w (∼p) ↔ ¬ Satisfies M w p := by
  -- Ambos lados se despliegan a Satisfies M w p → False
  rfl

/-- `◇p` es verdadera en `w` si `p` lo es en algún mundo accesible. La
dirección directa es el paso clásico `¬∀¬ ⟹ ∃`. -/
theorem satisfies_dia (M : KripkeModel VP) (w : M.World) (p : ModalFormula VP) :
    Satisfies M w (◇p) ↔ ∃ v : M.World, M.R w v ∧ Satisfies M v p := by
  constructor
  · -- (⟹) hdia dice que no ocurre que p falle en todo mundo accesible
    intro hdia
    by_contra hnex
    -- Aplicar hdia deja por probar que p falla en todo mundo accesible
    apply hdia
    intro v hRv hp
    -- Pero v es un mundo accesible donde vale p: un testigo, contra hnex
    exact hnex ⟨v, hRv, hp⟩
  · -- (⟸) El testigo v refuta que p falle en todo mundo accesible
    rintro ⟨v, hRv, hp⟩ hbox
    exact hbox v hRv hp

/-- Validez en un modelo: verdadera en todos sus mundos. -/
def ValidInModel (M : KripkeModel VP) (φ : ModalFormula VP) : Prop :=
  ∀ w : M.World, Satisfies M w φ

/-- Validez en un marco: válida en todo modelo sobre ese marco, es decir,
para cualquier valoración. No se usa en el desarrollo; se incluye por
completar la definición habitual. -/
def ValidInFrame (F : KripkeFrame) (φ : ModalFormula VP) : Prop :=
  ∀ V : F.World → VP → Prop, ValidInModel { toKripkeFrame := F, V := V } φ

/-- Validez: verdadera en todo mundo de todo modelo de Kripke. Es la noción
semántica que corresponde a la demostrabilidad en K. -/
def Valid (φ : ModalFormula VP) : Prop :=
  ∀ M : KripkeModel VP, ValidInModel M φ

-- Ejemplo: `φ ⟶ φ` es válida
example (φ : ModalFormula VP) : Valid (φ ⟶ φ) := by
  -- Fijados un modelo y un mundo cualesquiera, es inmediato
  intro M w hφ
  exact hφ


/-! ## 5. Corrección -/

/-- Lema puente: fijado un mundo `w`, la evaluación clásica con las
valoraciones "extraídas de `w`" (`v_atom x := M.V w x` y
`v_box ψ := Satisfies M w (□ψ)`) coincide con la satisfacción en `w`. -/
theorem cplEval_iff_satisfies (M : KripkeModel VP) (w : M.World)
    (φ : ModalFormula VP) :
    cplEval (fun x => M.V w x) (fun ψ => Satisfies M w (□ψ)) φ ↔
      Satisfies M w φ := by
  induction φ with
  | atom x => rfl
  | bot => rfl
  | imp φ ψ ihφ ihψ =>
      -- El objetivo es (A₁ → B₁) ↔ (A₂ → B₂) con ihφ : A₁ ↔ A₂ e ihψ : B₁ ↔ B₂
      apply Iff.intro
      · -- (⟹)
        intro h hφ
        exact ihψ.mp (h (ihφ.mpr hφ))
      · -- (⟸)
        intro h hφ
        exact ihψ.mpr (h (ihφ.mp hφ))
  | box φ ih =>
      -- cplEval (□φ) es v_box φ, elegida como Satisfies M w (□φ): no se usa ih
      rfl

/-- Las tautologías clásicas son válidas. -/
theorem valid_of_cpl_tautology {φ : ModalFormula VP} (h : IsCPLTautology φ) :
    Valid φ := by
  intro M w
  -- La tautología vale para toda valoración; en particular, para la de w
  have heval := h (fun x => M.V w x) (fun ψ => Satisfies M w (□ψ))
  -- El lema puente convierte esa evaluación en satisfacción
  exact (cplEval_iff_satisfies M w φ).mp heval

/-- El axioma K es válido: un modus ponens mundo a mundo. -/
theorem valid_axiom_k (φ ψ : ModalFormula VP) :
    Valid (□(φ ⟶ ψ) ⟶ (□φ ⟶ □ψ)) := by
  intro M w hboximp hboxφ v hRv
  -- Suponemos □(φ ⟶ ψ) y □φ en w, y tomamos un mundo v accesible
  -- En v valen φ ⟶ ψ y φ: modus ponens dentro de v
  exact hboximp v hRv (hboxφ v hRv)

/-- Modus ponens preserva la validez. -/
theorem valid_mp {φ ψ : ModalFormula VP} (hφψ : Valid (φ ⟶ ψ)) (hφ : Valid φ) :
    Valid ψ := by
  intro M w
  exact hφψ M w (hφ M w)

/-- Necesitación preserva la validez: si `φ` es verdadera en todos los
mundos, lo es en particular en los accesibles desde cualquiera. -/
theorem valid_nec {φ : ModalFormula VP} (hφ : Valid φ) :
    Valid (□φ) := by
  intro M w v hRv
  exact hφ M v

/-- Teorema de corrección: si `⊢ φ`, entonces `φ` es válida. Por inducción
sobre la derivación, con un caso por cada constructor de `Provable`. -/
theorem soundness {φ : ModalFormula VP} (h : Provable φ) : Valid φ := by
  induction h with
  | cpl φ htaut        => exact valid_of_cpl_tautology htaut
  | mp hφψ hφ ihφψ ihφ => exact valid_mp ihφψ ihφ
  | k φ ψ              => exact valid_axiom_k φ ψ
  | nec h ih           => exact valid_nec ih

/-- El modelo más simple: un único mundo, sin flechas y con valoración
falsa. -/
def trivialModel (VP : Type) : KripkeModel VP where
  World := Unit
  R := fun _ _ => False
  V := fun _ _ => False

/-- Consistencia de K: `⊥` no es demostrable. Si lo fuera, por corrección
sería verdadera en el único mundo de `trivialModel`, y no lo es. -/
theorem k_consistent : ¬ Provable (ModalFormula.bot : ModalFormula VP) := by
  intro hprov
  -- Por corrección, ⊥ sería verdadera en el mundo () del modelo trivial...
  have hsat : Satisfies (trivialModel VP) () ModalFormula.bot :=
    soundness hprov (trivialModel VP) ()
  -- ...pero Satisfies _ _ ⊥ es False por definición
  exact hsat


/-! ## 6. Completitud -/

/-! ### 6.1 Deducción a partir de hipótesis -/

/-- Deducibilidad desde un conjunto de hipótesis: `DeducibleFrom Γ φ`
formaliza `Γ ⊢ φ`. La necesitación no figura entre las reglas: solo actúa
sobre teoremas, y entra en las deducciones a través de `ax`. -/
inductive DeducibleFrom (Γ : Set (ModalFormula VP)) :
    ModalFormula VP → Prop where
  -- (ax) todo teorema de K puede invocarse en una deducción
  | ax  {φ : ModalFormula VP} (h : Provable φ) : DeducibleFrom Γ φ
  -- (mem) toda hipótesis de Γ puede usarse
  | mem {φ : ModalFormula VP} (h : φ ∈ Γ) : DeducibleFrom Γ φ
  -- (mp) modus ponens
  | mp  {φ ψ : ModalFormula VP} (hφψ : DeducibleFrom Γ (φ ⟶ ψ))
        (hφ : DeducibleFrom Γ φ) : DeducibleFrom Γ ψ

/-- Monotonía: agrandar el conjunto de hipótesis conserva las deducciones. -/
theorem deducibleFrom_mono {Γ Δ : Set (ModalFormula VP)} (hsub : Γ ⊆ Δ)
    {φ : ModalFormula VP} (h : DeducibleFrom Γ φ) : DeducibleFrom Δ φ := by
  induction h with
  | ax h            => exact DeducibleFrom.ax h
  | mem h           => exact DeducibleFrom.mem (hsub h)
  | mp _ _ ihφψ ihφ => exact DeducibleFrom.mp ihφψ ihφ

/-- Deducir sin hipótesis es exactamente demostrar en K. -/
theorem provable_of_deducibleFrom_empty {φ : ModalFormula VP}
    (h : DeducibleFrom (∅ : Set (ModalFormula VP)) φ) : Provable φ := by
  induction h with
  | ax h            => exact h
  | mem h           => simp at h  -- φ ∈ ∅ es imposible
  | mp _ _ ihφψ ihφ => exact Provable.mp ihφψ ihφ

/-- Teorema de deducción: si `Γ ∪ {φ} ⊢ ψ`, entonces `Γ ⊢ φ ⟶ ψ`. Por
inducción sobre la deducción, con las tautologías A1, identidad y A2. -/
theorem deduction_theorem {Γ : Set (ModalFormula VP)} {φ ψ : ModalFormula VP}
    (h : DeducibleFrom (insert φ Γ) ψ) : DeducibleFrom Γ (φ ⟶ ψ) := by
  induction h with
  | @ax χ hχ =>
      -- χ es un teorema: lo debilitamos con la tautología χ ⟶ (φ ⟶ χ)
      have hweak : DeducibleFrom Γ (χ ⟶ (φ ⟶ χ)) :=
        DeducibleFrom.ax (Provable.cpl _ (taut_weaken χ φ))
      exact DeducibleFrom.mp hweak (DeducibleFrom.ax hχ)
  | @mem χ hχ =>
      -- χ es una hipótesis de insert φ Γ: o es la propia φ, o ya estaba en Γ
      rcases Set.mem_insert_iff.mp hχ with heq | hmem
      · -- χ = φ: basta la identidad φ ⟶ φ
        subst heq
        exact DeducibleFrom.ax (Provable.cpl _ (taut_id _))
      · -- χ ∈ Γ: de nuevo, debilitamos
        have hweak : DeducibleFrom Γ (χ ⟶ (φ ⟶ χ)) :=
          DeducibleFrom.ax (Provable.cpl _ (taut_weaken χ φ))
        exact DeducibleFrom.mp hweak (DeducibleFrom.mem hmem)
  | @mp χ ξ _ _ ihχξ ihχ =>
      -- ihχξ : Γ ⊢ φ ⟶ (χ ⟶ ξ) e ihχ : Γ ⊢ φ ⟶ χ; la tautología A2 las combina
      have hdist : DeducibleFrom Γ ((φ ⟶ (χ ⟶ ξ)) ⟶ ((φ ⟶ χ) ⟶ (φ ⟶ ξ))) :=
        DeducibleFrom.ax (Provable.cpl _ (taut_dist φ χ ξ))
      exact DeducibleFrom.mp (DeducibleFrom.mp hdist ihχξ) ihχ

/-- Recíproco del teorema de deducción: monotonía más un modus ponens con la
nueva hipótesis. No se usa, pero completa el enunciado clásico. -/
theorem deduction_theorem_converse {Γ : Set (ModalFormula VP)}
    {φ ψ : ModalFormula VP} (h : DeducibleFrom Γ (φ ⟶ ψ)) :
    DeducibleFrom (insert φ Γ) ψ := by
  have h' : DeducibleFrom (insert φ Γ) (φ ⟶ ψ) :=
    deducibleFrom_mono (Set.subset_insert φ Γ) h
  exact DeducibleFrom.mp h' (DeducibleFrom.mem (Set.mem_insert φ Γ))


/-! ### 6.2 Consistencia y conjuntos maximales consistentes -/

/-- Un conjunto de fórmulas es consistente si de él no se deduce `⊥`. -/
def Consistent (Γ : Set (ModalFormula VP)) : Prop :=
  ¬ DeducibleFrom Γ ModalFormula.bot

/-- El vacío es consistente: corolario inmediato de `k_consistent`. -/
theorem consistent_empty : Consistent (∅ : Set (ModalFormula VP)) := by
  intro hbot
  exact k_consistent (provable_of_deducibleFrom_empty hbot)

/-- Si `φ` no se deduce de `Γ`, añadir `∼φ` a `Γ` conserva la consistencia. -/
theorem consistent_insert_neg {Γ : Set (ModalFormula VP)} {φ : ModalFormula VP}
    (h : ¬ DeducibleFrom Γ φ) : Consistent (insert (∼φ) Γ) := by
  intro hbot
  -- Teorema de deducción: Γ ⊢ ∼φ ⟶ ⊥, que por definición es ∼∼φ
  have hdneg : DeducibleFrom Γ (∼∼φ) := deduction_theorem hbot
  -- La doble negación clásica devuelve Γ ⊢ φ...
  have hdne : DeducibleFrom Γ (∼∼φ ⟶ φ) :=
    DeducibleFrom.ax (Provable.cpl _ (taut_dne φ))
  -- ...contra la hipótesis
  exact h (DeducibleFrom.mp hdne hdneg)

/-- Un conjunto es maximal consistente (MCS) si es consistente y toda
extensión consistente suya coincide con él. -/
def MaximalConsistent (Γ : Set (ModalFormula VP)) : Prop :=
  Consistent Γ ∧ ∀ Δ : Set (ModalFormula VP), Consistent Δ → Γ ⊆ Δ → Δ ⊆ Γ

/-- Clausura deductiva de los MCS: todo lo que `Γ` deduce, `Γ` lo contiene. -/
theorem mcs_mem_of_deducible {Γ : Set (ModalFormula VP)}
    (hΓ : MaximalConsistent Γ) {φ : ModalFormula VP} (h : DeducibleFrom Γ φ) :
    φ ∈ Γ := by
  -- insert φ Γ es consistente: si dedujera ⊥, Γ ⊢ φ ⟶ ⊥ y Γ ⊢ φ darían Γ ⊢ ⊥
  have hcons : Consistent (insert φ Γ) := by
    intro hbot
    have himp : DeducibleFrom Γ (φ ⟶ ModalFormula.bot) := deduction_theorem hbot
    exact hΓ.1 (DeducibleFrom.mp himp h)
  -- Por maximalidad, insert φ Γ ⊆ Γ; en particular, φ ∈ Γ
  exact hΓ.2 (insert φ Γ) hcons (Set.subset_insert φ Γ) (Set.mem_insert φ Γ)

/-- Completitud negacional: `Γ` contiene `φ` o `∼φ`, para toda `φ`. -/
theorem mcs_mem_or_neg_mem {Γ : Set (ModalFormula VP)}
    (hΓ : MaximalConsistent Γ) (φ : ModalFormula VP) : φ ∈ Γ ∨ ∼φ ∈ Γ := by
  -- Distinguimos si Γ deduce φ o no (razonamiento clásico)
  by_cases h : DeducibleFrom Γ φ
  · -- Si Γ ⊢ φ, la clausura deductiva da φ ∈ Γ
    exact Or.inl (mcs_mem_of_deducible hΓ h)
  · -- Si Γ ⊬ φ, añadir ∼φ conserva la consistencia y la maximalidad da ∼φ ∈ Γ
    have hcons : Consistent (insert (∼φ) Γ) := consistent_insert_neg h
    exact Or.inr (hΓ.2 _ hcons (Set.subset_insert _ _) (Set.mem_insert _ _))

/-- La disyunción anterior es excluyente: `∼φ ∈ Γ` si y solo si `φ ∉ Γ`. -/
theorem mcs_neg_mem_iff {Γ : Set (ModalFormula VP)} (hΓ : MaximalConsistent Γ)
    (φ : ModalFormula VP) : ∼φ ∈ Γ ↔ φ ∉ Γ := by
  constructor
  · -- (⟹) Con ∼φ y φ en Γ, modus ponens da Γ ⊢ ⊥ (∼φ es φ ⟶ ⊥)
    intro hnφ hφ
    exact hΓ.1 (DeducibleFrom.mp (DeducibleFrom.mem hnφ) (DeducibleFrom.mem hφ))
  · -- (⟸) Si φ ∉ Γ, la completitud negacional fuerza ∼φ ∈ Γ
    intro hφ
    rcases mcs_mem_or_neg_mem hΓ φ with h | h
    · exact absurd h hφ
    · exact h

/-- La pertenencia de una implicación se comporta como una implicación:
`(φ ⟶ ψ) ∈ Γ ↔ (φ ∈ Γ → ψ ∈ Γ)`. -/
theorem mcs_imp_mem_iff {Γ : Set (ModalFormula VP)} (hΓ : MaximalConsistent Γ)
    {φ ψ : ModalFormula VP} : (φ ⟶ ψ) ∈ Γ ↔ (φ ∈ Γ → ψ ∈ Γ) := by
  constructor
  · -- (⟹) Con φ ⟶ ψ y φ en Γ, modus ponens deduce ψ, y Γ es cerrado
    intro himp hφ
    exact mcs_mem_of_deducible hΓ
      (DeducibleFrom.mp (DeducibleFrom.mem himp) (DeducibleFrom.mem hφ))
  · -- (⟸) Distinguimos si φ ∈ Γ
    intro h
    by_cases hφ : φ ∈ Γ
    · -- Si φ ∈ Γ, entonces ψ ∈ Γ; debilitando, Γ ⊢ φ ⟶ ψ
      have hweak : DeducibleFrom Γ (ψ ⟶ (φ ⟶ ψ)) :=
        DeducibleFrom.ax (Provable.cpl _ (taut_weaken ψ φ))
      exact mcs_mem_of_deducible hΓ
        (DeducibleFrom.mp hweak (DeducibleFrom.mem (h hφ)))
    · -- Si φ ∉ Γ, entonces ∼φ ∈ Γ; por explosión, Γ ⊢ φ ⟶ ψ
      have hnφ : ∼φ ∈ Γ := (mcs_neg_mem_iff hΓ φ).mpr hφ
      have hexf : DeducibleFrom Γ (∼φ ⟶ (φ ⟶ ψ)) :=
        DeducibleFrom.ax (Provable.cpl _ (taut_exfalso φ ψ))
      exact mcs_mem_of_deducible hΓ
        (DeducibleFrom.mp hexf (DeducibleFrom.mem hnφ))


/-! ### 6.3 El lema de Lindenbaum -/

/-- Lo que se deduce de la unión de una cadena de conjuntos se deducía ya de
algún eslabón. Es la "finitud de las deducciones" en miniatura: cada modus
ponens funde los eslabones de sus dos premisas en uno solo. -/
theorem deducibleFrom_sUnion_chain {c : Set (Set (ModalFormula VP))}
    (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) {φ : ModalFormula VP}
    (h : DeducibleFrom (⋃₀ c) φ) : ∃ Δ ∈ c, DeducibleFrom Δ φ := by
  induction h with
  | @ax χ hχ =>
      -- Un teorema se deduce desde cualquier eslabón, y la cadena no es vacía
      obtain ⟨Δ, hΔ⟩ := hne
      exact ⟨Δ, hΔ, DeducibleFrom.ax hχ⟩
  | @mem χ hχ =>
      -- Una hipótesis de la unión pertenece a algún eslabón
      obtain ⟨Δ, hΔc, hmem⟩ := Set.mem_sUnion.mp hχ
      exact ⟨Δ, hΔc, DeducibleFrom.mem hmem⟩
  | @mp χ ξ _ _ ihχξ ihχ =>
      -- Cada premisa vive en su propio eslabón...
      obtain ⟨Δ₁, hΔ₁, hd₁⟩ := ihχξ
      obtain ⟨Δ₂, hΔ₂, hd₂⟩ := ihχ
      -- ...y, al estar encadenados, ambas caben en el mayor de los dos
      rcases eq_or_ne Δ₁ Δ₂ with rfl | hneq
      · -- Mismo eslabón: modus ponens directamente
        exact ⟨_, hΔ₁, DeducibleFrom.mp hd₁ hd₂⟩
      · -- Eslabones distintos: la propiedad de cadena los compara
        rcases hchain hΔ₁ hΔ₂ hneq with hsub | hsub
        · exact ⟨Δ₂, hΔ₂, DeducibleFrom.mp (deducibleFrom_mono hsub hd₁) hd₂⟩
        · exact ⟨Δ₁, hΔ₁, DeducibleFrom.mp hd₁ (deducibleFrom_mono hsub hd₂)⟩

/-- Lema de Lindenbaum: todo conjunto consistente se extiende a un MCS. Se
aplica el lema de Zorn a la familia de los conjuntos consistentes, ordenada
por inclusión: la cota superior de una cadena es su unión, consistente por
el lema anterior. No requiere que `VP` sea numerable. -/
theorem lindenbaum {Γ : Set (ModalFormula VP)} (hΓ : Consistent Γ) :
    ∃ Δ : Set (ModalFormula VP), Γ ⊆ Δ ∧ MaximalConsistent Δ := by
  -- Condición de cadenas que exige zorn_subset_nonempty
  have hchains : ∀ c ⊆ {Θ : Set (ModalFormula VP) | Consistent Θ},
      IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {Θ : Set (ModalFormula VP) | Consistent Θ}, ∀ Δ ∈ c, Δ ⊆ ub := by
    intro c hcS hchain hne
    -- La cota superior es la unión de la cadena; falta ver que es consistente
    refine ⟨⋃₀ c, ?_, fun Δ hΔ => Set.subset_sUnion_of_mem hΔ⟩
    -- Si la unión dedujera ⊥, algún eslabón lo deduciría, y son consistentes
    intro hbot
    obtain ⟨Δ, hΔc, hΔbot⟩ := deducibleFrom_sUnion_chain hchain hne hbot
    exact hcS hΔc hΔbot
  -- Zorn sobre la familia de los consistentes, partiendo de Γ
  obtain ⟨Δ, hΓΔ, hΔmax⟩ :=
    zorn_subset_nonempty {Θ : Set (ModalFormula VP) | Consistent Θ}
      hchains Γ hΓ
  -- El maximal que devuelve Zorn es exactamente un MCS según la definición
  refine ⟨Δ, hΓΔ, hΔmax.1, ?_⟩
  intro Θ hΘ hsubΘ
  exact hΔmax.2 hΘ hsubΘ


/-! ### 6.4 El modelo canónico -/

/-- El modelo canónico. Sus mundos son todos los MCS; desde `Γ` se accede a
`Δ` cuando `Δ` cumple todas las obligaciones modales de `Γ` (si `□ψ ∈ Γ`,
entonces `ψ ∈ Δ`); y una variable es verdadera en el mundo `Γ` cuando, vista
como fórmula, pertenece a `Γ`. -/
def canonicalModel (VP : Type) : KripkeModel VP where
  World := { Γ : Set (ModalFormula VP) // MaximalConsistent Γ }
  R := fun Γ Δ => ∀ ψ : ModalFormula VP, □ψ ∈ Γ.val → ψ ∈ Δ.val
  V := fun Γ x => ModalFormula.atom x ∈ Γ.val

/-- Lema de encajonado: si `φ` se deduce de las fórmulas desencajonadas de
`Γ` (las `ψ` con `□ψ ∈ Γ`), entonces `□φ` se deduce de `Γ`. Cada regla se
"encajona": `ax` con la necesitación, `mem` directamente y `mp` con K. -/
theorem deducibleFrom_box {Γ : Set (ModalFormula VP)} {φ : ModalFormula VP}
    (h : DeducibleFrom {ψ : ModalFormula VP | □ψ ∈ Γ} φ) :
    DeducibleFrom Γ (□φ) := by
  induction h with
  | @ax χ hχ =>
      -- χ es un teorema de K: por necesitación, □χ también lo es
      exact DeducibleFrom.ax (Provable.nec hχ)
  | @mem χ hχ =>
      -- hχ dice, leído con cuidado, exactamente que □χ ∈ Γ
      exact DeducibleFrom.mem hχ
  | @mp χ ξ _ _ ihχξ ihχ =>
      -- Tenemos Γ ⊢ □(χ ⟶ ξ) y Γ ⊢ □χ; el axioma K y dos modus ponens rematan
      have hK : DeducibleFrom Γ (□(χ ⟶ ξ) ⟶ (□χ ⟶ □ξ)) :=
        DeducibleFrom.ax (Provable.k χ ξ)
      exact DeducibleFrom.mp (DeducibleFrom.mp hK ihχξ) ihχ


/-! ### 6.5 Los lemas de existencia y de verdad -/

/-- Lema de existencia: si `Γ` es un MCS y `□φ ∉ Γ`, existe un MCS `Δ`
accesible desde `Γ` (cumple sus obligaciones modales) con `φ ∉ Δ`. Se
construye extendiendo con Lindenbaum el conjunto de las obligaciones de `Γ`
más `∼φ`. -/
theorem existence_lemma {Γ : Set (ModalFormula VP)} (hΓ : MaximalConsistent Γ)
    {φ : ModalFormula VP} (hbox : □φ ∉ Γ) :
    ∃ Δ : Set (ModalFormula VP),
      MaximalConsistent Δ ∧ (∀ ψ : ModalFormula VP, □ψ ∈ Γ → ψ ∈ Δ) ∧
        φ ∉ Δ := by
  -- (1) φ no se deduce de las obligaciones (encajonado más clausura deductiva)
  have hnφ : ¬ DeducibleFrom {ψ : ModalFormula VP | □ψ ∈ Γ} φ := by
    intro hdφ
    exact hbox (mcs_mem_of_deducible hΓ (deducibleFrom_box hdφ))
  -- (2) Añadir ∼φ a las obligaciones conserva la consistencia
  have hcons : Consistent (insert (∼φ) {ψ : ModalFormula VP | □ψ ∈ Γ}) :=
    consistent_insert_neg hnφ
  -- (3) Lindenbaum extiende ese conjunto a un MCS Δ
  obtain ⟨Δ, hsub, hΔ⟩ := lindenbaum hcons
  refine ⟨Δ, hΔ, ?_, ?_⟩
  · -- Δ contiene las obligaciones de Γ: ya estaban antes de extender
    intro ψ hψ
    have hψ' : ψ ∈ {χ : ModalFormula VP | □χ ∈ Γ} := hψ
    exact hsub (Set.mem_insert_of_mem _ hψ')
  · -- φ ∉ Δ: en Δ está ∼φ, y φ y ∼φ no caben juntas en un consistente
    intro hφΔ
    have hnφΔ : ∼φ ∈ Δ := hsub (Set.mem_insert _ _)
    exact hΔ.1
      (DeducibleFrom.mp (DeducibleFrom.mem hnφΔ) (DeducibleFrom.mem hφΔ))

/-- Lema de verdad: en el modelo canónico, ser verdadera en el mundo `Γ` y
pertenecer al conjunto `Γ` coinciden para toda fórmula. Por inducción sobre
la fórmula, generalizando el mundo. -/
theorem truth_lemma (φ : ModalFormula VP) (Γ : (canonicalModel VP).World) :
    Satisfies (canonicalModel VP) Γ φ ↔ φ ∈ Γ.val := by
  induction φ generalizing Γ with
  | atom x =>
      -- Por definición de la valoración canónica
      exact Iff.rfl
  | bot =>
      constructor
      · -- ⊥ no se satisface en ningún mundo...
        intro h
        exact False.elim h
      · -- ...ni puede pertenecer a un conjunto consistente: daría Γ ⊢ ⊥
        intro h
        exact False.elim (Γ.property.1 (DeducibleFrom.mem h))
  | imp φ ψ ihφ ihψ =>
      -- Ambos lados son implicaciones; las hipótesis de inducción las cruzan
      constructor
      · intro hsat
        apply (mcs_imp_mem_iff Γ.property).mpr
        intro hφ
        exact (ihψ Γ).mp (hsat ((ihφ Γ).mpr hφ))
      · intro hmem hφ
        exact (ihψ Γ).mpr ((mcs_imp_mem_iff Γ.property).mp hmem ((ihφ Γ).mp hφ))
  | box φ ih =>
      constructor
      · -- (⟹) Por reducción al absurdo, con el lema de existencia
        intro hsat
        by_contra hbox
        obtain ⟨Δ, hΔmcs, hR, hnφ⟩ := existence_lemma Γ.property hbox
        exact hnφ ((ih ⟨Δ, hΔmcs⟩).mp (hsat ⟨Δ, hΔmcs⟩ hR))
      · -- (⟸) La accesibilidad canónica reparte φ a todo mundo accesible
        intro hbox Δ hR
        exact (ih Δ).mpr (hR φ hbox)


/-! ### 6.6 Completitud y adecuación -/

/-- Teorema de completitud: si `φ` es válida, entonces `⊢ φ`. Por reducción
al absurdo: si `φ` no es demostrable, `{∼φ}` es consistente y se extiende a
un MCS `Γ`; en el mundo `Γ` del modelo canónico, `φ` es verdadera por validez
y falsa por el lema de verdad. -/
theorem completeness {φ : ModalFormula VP} (h : Valid φ) : Provable φ := by
  by_contra hnφ
  -- (1) φ no se deduce sin hipótesis...
  have hnd : ¬ DeducibleFrom (∅ : Set (ModalFormula VP)) φ := by
    intro hd
    exact hnφ (provable_of_deducibleFrom_empty hd)
  -- (2) ...luego {∼φ} es consistente...
  have hcons : Consistent (insert (∼φ) (∅ : Set (ModalFormula VP))) :=
    consistent_insert_neg hnd
  -- (3) ...y Lindenbaum lo extiende a un MCS Γ con ∼φ ∈ Γ
  obtain ⟨Γ, hsub, hΓ⟩ := lindenbaum hcons
  have hnφΓ : ∼φ ∈ Γ := hsub (Set.mem_insert _ _)
  -- (4) Γ es un mundo del modelo canónico; como φ es válida, se satisface en él
  have hsat : Satisfies (canonicalModel VP) ⟨Γ, hΓ⟩ φ :=
    h (canonicalModel VP) ⟨Γ, hΓ⟩
  -- (5) El lema de verdad convierte esa satisfacción en φ ∈ Γ
  have hφΓ : φ ∈ Γ := (truth_lemma φ ⟨Γ, hΓ⟩).mp hsat
  -- (6) Pero φ y ∼φ juntas producen Γ ⊢ ⊥, contra la consistencia de Γ
  exact hΓ.1 (DeducibleFrom.mp (DeducibleFrom.mem hnφΓ) (DeducibleFrom.mem hφΓ))

/-- Teorema de adecuación: la demostrabilidad en K y la validez en los
modelos de Kripke son exactamente la misma noción. -/
theorem provable_iff_valid (φ : ModalFormula VP) : Provable φ ↔ Valid φ :=
  ⟨soundness, completeness⟩
