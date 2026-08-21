# מה עשית בפרקים 1.6–1.8 — הסבר מלא

מסמך מלווה ל‑`LinerAlgbra/chapter1_6.lean`, `chapter1_7.lean`, `chapter1_8.lean`.
כל הגדרה, כל הוכחה, וכל טריק — למה הוא שם ומה הוא חוסך.

---

## תמונת מצב בשורה אחת

ב‑1.6 קבעת ש**מטריצה היא לא טיפוס חדש**.
ב‑1.7 קבעת ש**פעולה אלמנטרית היא נתון, לא פעולה**.
ב‑1.8 קבעת ש**פעולה על מטריצה היא אותה פעולה על מערכת, בתחפושת**.

שלוש ההחלטות האלה הן הסיבה שהקוד שלך הוא ~700 שורות ולא ~2000. נפרק אותן.

---

# פרק 1.6 — מטריצות

## שלוש ההגדרות

```lean
def CoefficientMatrix (sys : LinearSystem A m n) : Ntuple (Ntuple A n) m :=
  fun row => (sys.equations row).a

def FreeCoefficientVector (sys : LinearSystem A m n) : Ntuple A m :=
  fun row => (sys.equations row).b

def AugmentedMatrix (sys : LinearSystem A m n) : Ntuple (Ntuple A (n + 1)) m :=
  fun row column =>
    if h : column.val < n then
      (sys.equations row).a ⟨column.val, h⟩
    else
      (sys.equations row).b
```

### טריק 1 — מטריצה היא n‑יה של n‑יות

לא הגדרת `structure Matrix`. כתבת:

```
Ntuple (Ntuple A n) m   =   Fin m → (Fin n → A)   =   Fin m → Fin n → A
```

מטריצה היא פשוט פונקציה משורה לשורה. למה זה חכם:

1. **כל מה שהוכחת ב‑1.3 על `Ntuple` חל אוטומטית על כל שורה.** `Ntuple_add`, `Ntuple_smul`, אסוציאטיביות, פילוג — הכול זמין לשורות בלי שורת קוד אחת נוספת. אם היית מגדיר `structure Matrix` היית צריך להוכיח הכול מחדש.
2. **אין `.entries` ואין `.mk`.** `M i j` פשוט עובד. שוויון מטריצות נסגר ב‑`funext row column`, וזה בדיוק מה שאתה עושה בכל הוכחה בהמשך.
3. `AugmentedMatrix` יכולה להחזיר `Ntuple (Ntuple A (n+1)) m` בלי שום המרה — רק שינוי במספר.

### טריק 2 — `dite` (ה‑`if` התלוי)

תסתכל שוב על השורה:

```lean
if h : column.val < n then
  (sys.equations row).a ⟨column.val, h⟩
```

שים לב ל‑`h :` אחרי ה‑`if`. זה **לא** `ite` רגיל, זה `dite` — "dependent if".

הבעיה שהוא פותר: `(sys.equations row).a` היא `Ntuple A n`, כלומר `Fin n → A`. יש לך ביד `column : Fin (n+1)`. אתה **לא יכול** להאכיל אותה לפונקציה — הטיפוסים לא מסתדרים. כדי לבנות `Fin n` אתה צריך זוג: המספר `column.val`, **ועדות** שהוא קטן מ‑`n`.

מאיפה תשיג את העדות? מהתנאי של ה‑`if` עצמו. `dite` נותן לך שם (`h`) לעובדה שהתנאי התקיים, בתוך הענף החיובי. ואז `⟨column.val, h⟩ : Fin n` נבנה.

זה דפוס שתשתמש בו הרבה: **כשאתה צריך הוכחה כדי לבנות אובייקט, תפיק אותה מהפיצול עצמו.**

בענף ה‑`else` אתה יודע ש‑`¬(column.val < n)`, וביחד עם `column.isLt : column.val < n+1` נובע `column.val = n` — כלומר זו העמודה האחרונה, המקדם החופשי. בדיוק זה מה שיצטרך `omega` לגזור בהוכחה בפרק 1.8.

---

# פרק 1.7 — מערכות שקולות ופעולות אלמנטריות

## ההגדרה המרכזית

```lean
def AreEquivalent {m₁ m₂ n : Nat}
    (One : LinearSystem A m₁ n) (Two : LinearSystem A m₂ n) : Prop :=
  ∀ x : Ntuple A n, IsSystemSolution One x ↔ IsSystemSolution Two x
```

זו בדיוק הגדרה 1.7.1 בספר (עמ' 63): אותה קבוצת פתרונות.

### טריק 3 — `m₁` ו‑`m₂` נפרדים

הספר מדבר על שתי מערכות ב‑`n` משתנים ולא מקפיד על מספר המשוואות. אתה קידדת את זה נאמנה: **מספר המשוואות רשאי להיות שונה**, רק מספר הנעלמים חייב להתאים.

זה נראה כמו פרט טכני והוא לא. בשיטת החילוץ שורות מתאפסות ונזרקות — מערכת של 4 משוואות הופכת למערכת של 2. עם `AreEquivalent` שדורש `m₁ = m₂` היית תקוע בפרק 1.12. עם ההגדרה שלך זה עובד.

## ארבע הפעולות

```lean
def switch (m n) (sys) (t1 t2 : Fin m) : LinearSystem A m n :=
  { equations := fun k =>
      if k = t1 then sys.equations t2
      else if k = t2 then sys.equations t1
      else sys.equations k }

def replaceRow (sys) (i : Fin m) (newEq : LinearEquation A n) := ...
def scaleRow   (sys) (i : Fin m) (c : A) := ...
def addRow     (sys) (i j : Fin m) (c : A) := ...
```

כולן באותו דפוס: **בונים פונקציה חדשה שמסכימה עם הישנה בכל מקום חוץ מבמקום אחד.**
זה `Function.update` בעצם, כתוב ידנית. אין העתקה, אין מוטציה — יש פונקציה חדשה.

שים לב ש‑`switch` מטפלת נכון גם במקרה `t1 = t2` (אז היא הזהות), בלי שהיה צריך תנאי מיוחד. זה יוצא בחינם מהסדר של ה‑`if`ים.

> **הערה:** `replaceRow` מוגדרת ואף פעם לא בשימוש. כתבת בעצמך בהערות בתוך `addRow` שאפשר היה להביע אותה דרך `scaleRow`. אם תרצה לנקות — `scaleRow` ו‑`addRow` שתיהן מקרים פרטיים של `replaceRow`, וזה היה מקצר.

## שלוש הוכחות השקילות — הדפוס המשותף

`SwitchIsEquivalent`, `ScaleRowIsEquivalent`, `AddRowIsEquivalent` בנויות אותו דבר:

```lean
have op_eq (k : Fin m) : (theOperation ...).equations k = if k = i then ... else ... := by
  rfl
```

### טריק 4 — "למת החישוב" עם `rfl`

זה טריק שכדאי שתזהה כי הוא חוזר בכל הקובץ.

הבעיה: ההגדרה של `scaleRow` היא *מבנית* — Lean יודע שהיא שווה לביטוי ה‑`if` **לפי הגדרה**. אבל `rw` לא עובד עם "לפי הגדרה", הוא צריך `Eq` מפורש שאפשר לאחוז בו. `unfold` היה עובד אבל פותח הכול ומלכלך את היעד.

הפתרון שלך: מנסחים את העובדה כלמה מקומית שההוכחה שלה היא `rfl`, ואז יש בידך `Eq` נקי לעשות בו `rw [op_eq k]` בדיוק היכן שאתה רוצה. **הפכת עובדה הגדרתית לכלי עבודה.**

### הדפוס `by_cases` — שורה שהשתנתה מול שורה שלא

```lean
by_cases hki : k = i
· rw [hki, if_pos rfl]   -- זו השורה ששינינו: כאן העבודה האמיתית
· rw [if_neg hki]
  exact h k              -- שורה שלא נגענו בה: הפתרון פותר אותה כמו קודם
```

זה בדיוק הטיעון של הספר, מילה במילה: *"השינוי משנה רק את המשוואה ה‑i של המערכת"*. הענף השני תמיד טריוויאלי. כל התוכן בענף הראשון.

### כאן 1.4 משתלם — ההוכחה הכי יפה בקובץ

הכיוון ⇒ של `AddRowIsEquivalent`, אחרי כל ההכנות, הוא **שורה אחת**:

```lean
rw [dot_product_add, dot_product_smul, h i, h j]
```

תקרא אותה לאט. היעד הוא
$$\langle a_i + c\,a_j,\ x\rangle = b_i + c\,b_j$$

- `dot_product_add` מפצל את המכפלה הסקלרית של סכום → $\langle a_i,x\rangle + \langle c\,a_j,x\rangle$
- `dot_product_smul` מוציא את הסקלר → $\langle a_i,x\rangle + c\langle a_j,x\rangle$
- `h i` אומר $\langle a_i,x\rangle = b_i$
- `h j` אומר $\langle a_j,x\rangle = b_j$

ונשאר $b_i + c\,b_j$. סוף.

**זו התשואה על 80 השורות המכוערות שכתבת ב‑`chapter1_4.lean`.** האינדוקציות המייגעות שם, עם כל ה‑`Nat.lt_trans i.isLt (Nat.lt_succ_self k)`, קיימות בדיוק כדי שהשורה הזאת תעבוד. זה הרעיון של בניית תשתית: משלמים פעם אחת בעומק, גובים בכל שימוש.

### `change` — מתי ולמה

```lean
change Ntuple_dot_product (Ntuple_add (sys.equations i).a ...) x = ... at hk
```

`change` מחליף את היעד (או השערה) בביטוי **שווה לפי הגדרה** אבל כתוב אחרת.

למה נזקקת לו: אחרי `if_pos` היעד מכיל `({ a := ..., b := ... } : LinearEquation A n).a` — הטלה של שדה על קונסטרוקטור אנונימי. Lean יודע שזה פשוט `...`, אבל `rw [dot_product_add]` מחפש התאמה *תחבירית* ולא מוצא. `change` מיישר את התחביר ואז ה‑`rw` תופס.

(ב‑`ScaleRowIsEquivalent` פתרת את אותו דבר עם `have h1 : ... := by rfl` ואז `rw [h1]` — אותו רעיון בדיוק, ניסוח אחר.)

### איפה ההנחות באמת נחוצות

שווה שתשים לב, כי זו המתמטיקה ולא ה‑Lean:

- **`hc : c ≠ 0` ב‑`scaleRow`** — נחוץ רק בכיוון ⇐. שם אתה בונה `inv c hc` ומשתמש ב‑`MulInverseCancel`. בלי זה, כפל שורה ב‑0 הופך אותה ל‑`0 = 0` והמערכת החדשה מקבלת פתרונות שהמקורית דחתה.
- **`hij : i ≠ j` ב‑`addRow`** — נחוץ כדי לדעת ש**שורה `j` לא השתנתה** (`rw [add_eq j, if_neg hji]`). זה בדיוק מה שהספר דורש: *"הוספת כפולה בסקלר של אחת ממשוואות המערכת ל**משוואה אחרת**"*. אם `i = j`, הפעולה היא $R_i \to (1+c)R_i$, וב‑$c = -1$ היא מוחקת את השורה.

## `ElementaryOperation` — הטריק הכי חכם בקובץ

```lean
inductive ElementaryOperation (A : Type) [Field_ A] (m n : Nat) where
  | switchRows (i j : Fin m)
  | scaleRow   (i : Fin m) (c : A) (hc : c ≠ Field_.zero)
  | addRow     (i j : Fin m) (c : A) (hij : i ≠ j)
```

### טריק 5 — פעולה היא נתון, לא פונקציה

עד לרגע הזה `switch`, `scaleRow`, `addRow` היו **פונקציות**. אי אפשר לשים פונקציות ברשימה ולעשות עליה אינדוקציה בצורה שימושית, ואי אפשר לשאול "מה ההופכית של הפונקציה הזאת".

הפכת אותן ל**ערכים** של טיפוס אינדוקטיבי. עכשיו פעולה אלמנטרית היא אובייקט שאפשר להעביר, לאחסן, לרשום ברשימה, לעשות עליו `cases`, ולהגדיר עליו פונקציות. כל 1.8 נשען על זה.

### טריק 6 — ההנחות יושבות בתוך הקונסטרוקטור

זה החלק המתוחכם, ואולי לא שמת לב כמה הוא חזק.

`scaleRow` דורש `hc : c ≠ Field_.zero` **כשדה של הקונסטרוקטור**. המשמעות: **אי אפשר בכלל לבנות פעולת כפל־שורה לא חוקית.** לא "אפשר אבל אז המשפט לא יחול" — פשוט אי אפשר לכתוב את זה, זו שגיאת טיפוסים.

ההשלכות:

1. `applyElementaryOperation` לא צריכה לבדוק כלום. היא כותבת `_hc` ומתעלמת — ההגדרה של `scaleRow` לא זקוקה לזה.
2. `elementaryOperation_equivalent` עושה `cases op` והשם `hc` פשוט **קיים** בהקשר, מוכן להגשה ל‑`ScaleRowIsEquivalent`:

```lean
theorem elementaryOperation_equivalent (op) (sys) :
    AreEquivalent sys (applyElementaryOperation op sys) := by
  cases op with
  | switchRows i j    => exact SwitchIsEquivalent m n sys i j
  | scaleRow i c hc   => exact ScaleRowIsEquivalent sys i c hc
  | addRow i j c hij  => exact AddRowIsEquivalent sys i j c hij
```

שלוש שורות. אין `by_cases`, אין תנאים, אין מקרי קצה — כי הטיפוס כבר מנע אותם. זה נקרא *making illegal states unrepresentable*, וזה מה שעשית.

3. הרווח האמיתי מגיע ב‑1.8: `RowEquivalent` מוגדר עם `ops : Ntuple (ElementaryOperation A m n) length`. **כל סדרה כזאת חוקית אוטומטית.** לא צריך להוסיף ל‑`RowEquivalent` תנאי "וכל הפעולות בסדרה חוקיות".

> הערה קטנה: הפרמטר `n` ב‑`ElementaryOperation` לא מופיע באף קונסטרוקטור. הוא "פנטום" — קיים רק כדי שהטיפוס יתאים למערכת. זה עובד, אבל זה מסביר למה לפעמים Lean מתקשה להסיק אותו.

## `applySequence` — סדרה סופית של פעולות

```lean
def applySequence (length : Nat) (operations : Ntuple (ElementaryOperation A m n) length)
    (initialSystem : LinearSystem A m n) : LinearSystem A m n :=
  match length with
  | 0     => initialSystem
  | k + 1 =>
      let previousOperations := fun index => operations ⟨index.val, ...⟩
      let systemAfterPrevious := applySequence k previousOperations initialSystem
      let lastOperation := operations ⟨k, Nat.lt_succ_self k⟩
      applyElementaryOperation lastOperation systemAfterPrevious
```

**סדר ההפעלה:** אינדקס 0 ראשון, אינדקס `length-1` אחרון. הרקורסיה קולפת מהסוף: מפעילה את `0..k-1` ואז את `k`.

`previousOperations` היא הקיצוץ של הסדרה ל‑`k` הראשונים. כתבת אותה ידנית עם `Nat.lt_trans index.isLt (Nat.lt_succ_self k)` — ב‑Mathlib זו `Fin.init` או `i.castSucc`, וזה היה מקצר לך המון בהמשך.

## `FiniteElementaryOperationsEquivalent` — הטכניקה הכי חשובה ללמוד

זה משפט 1.7.3 בספר. ותסתכל טוב על הניסוח:

```lean
theorem FiniteElementaryOperationsEquivalent (sys : LinearSystem A m n) (r : Nat) :
    ∀ ops : Ntuple (ElementaryOperation A m n) r,
      AreEquivalent sys (applySequence r ops sys) := by
  induction r with ...
```

### טריק 7 — `∀ ops` נמצא **אחרי** הנקודתיים ולא בפרמטרים

זה ההבדל בין הוכחה שעובדת להוכחה שנתקעת, ואני לא בטוח שזה היה מכוון — אבל זה נכון.

אילו כתבת `(ops : Ntuple (ElementaryOperation A m n) r)` כפרמטר לפני הנקודתיים, אז ברגע ש‑`induction r` מפצל למקרה `k+1`, הנחת האינדוקציה הייתה מדברת על **אותו** `ops` — שהטיפוס שלו תלוי ב‑`r`. וזה לא מה שאתה צריך: אתה צריך להפעיל את הנחת האינדוקציה על **סדרה אחרת**, המקוצצת, באורך `k`.

כשה‑`∀` בתוך הטענה, הנחת האינדוקציה יוצאת:

```
ih : ∀ ops : Ntuple (ElementaryOperation A m n) k, AreEquivalent sys (applySequence k ops sys)
```

וזה בדיוק מה שצריך — היא חלה על כל סדרה באורך `k`, כולל המקוצצת. בשורה

```lean
ih (fun i => ops ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
```

אתה גובה את התשלום.

**הכלל:** לפני `induction`, הכלל כל מה שתלוי במשתנה שעליו אתה עושה אינדוקציה. בטקטיקות זה `generalize` או `revert`; בניסוח זה `∀` אחרי הנקודתיים.

ואז שאר ההוכחה היא בדיוק הטיעון של הספר: *שקילות של `k` הצעדים הראשונים* + *שקילות של הצעד האחרון* + `AreEquivalent_trans`.

---

# פרק 1.8 — מטריצות שקולות־שורה

## האיזומורפיזם

```lean
def systemFromAugmentedMatrix (matrix : Ntuple (Ntuple A (n + 1)) m) : LinearSystem A m n :=
  { equations := fun row =>
      { a := fun column => matrix row ⟨column.val, Nat.lt_trans column.isLt (Nat.lt_succ_self n)⟩
        b := matrix row ⟨n, Nat.lt_succ_self n⟩ } }
```

זו ההופכית של `AugmentedMatrix` מ‑1.6: `n` העמודות הראשונות → מקדמים, האחרונה → איבר חופשי. וכאן ההמרה הפוכה: אתה מרים `column : Fin n` ל‑`Fin (n+1)` ע"י `Nat.lt_trans column.isLt (Nat.lt_succ_self n)` — כלומר "אם `c < n` ו‑`n < n+1` אז `c < n+1`". (ב‑Mathlib: `Fin.castSucc`.)

ואז שני המשפטים שהופכים את זה לאיזומורפיזם ממש:

```lean
theorem systemFromAugmentedMatrix_AugmentedMatrix (system) :
    systemFromAugmentedMatrix (AugmentedMatrix system) = system
theorem AugmentedMatrix_systemFromAugmentedMatrix (matrix) :
    AugmentedMatrix (systemFromAugmentedMatrix matrix) = matrix
```

הראשון: `cases system with | mk equations => simp [...]`. ה‑`cases` על מבנה בעל שדה יחיד הוא **אטא־הרחבה** — הוא מחליף את `system` ב‑`⟨equations⟩` כך ש‑`simp` רואה דרך ההטלות.

השני מעניין יותר:

```lean
funext row column
unfold AugmentedMatrix systemFromAugmentedMatrix
split
· rfl
· have columnIsLast : column.val = n := by omega
  have columnEquality : column = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext columnIsLast
  rw [columnEquality]
```

- `split` מפצל את ה‑`dite` משני הענפים.
- בענף החיובי: `rfl`. הרכבנו והפרדנו את אותו איבר — זהה מילולית.
- בענף השלילי: יש לך `¬(column.val < n)` בהקשר, ו‑`column.isLt : column.val < n + 1` מובנה ב‑`Fin`. `omega` מסיק `column.val = n`. ואז `Fin.ext` — **שני `Fin` שווים אם ורק אם ה‑`val` שלהם שווה, ההוכחות לא משנות** (proof irrelevance). זה למה `Fin.ext` קיים ולמה אתה זקוק לו כל הזמן.

## הטריק המרכזי של 1.8 — הצמדה (conjugation)

```lean
def applyMatrixElementaryOperation (operation) (matrix) :=
  AugmentedMatrix (applyElementaryOperation operation (systemFromAugmentedMatrix matrix))

def applyMatrixSequence (length) (operations) (initialMatrix) :=
  AugmentedMatrix (applySequence length operations (systemFromAugmentedMatrix initialMatrix))
```

### טריק 8 — לא הגדרת אף פעולת שורה מחדש

הספר מציג את פעולות השורה כאובייקט חדש: $R_i \leftrightarrow R_j$, $R_i \to tR_i$, $R_i \to R_i + tR_j$ **על מטריצות**. הדרך הנאיבית: להגדיר שלוש פונקציות חדשות על `Ntuple (Ntuple A (n+1)) m`, ואז להוכיח מחדש שהן שומרות פתרונות. זה היה מכפיל את הקובץ.

מה שעשית במקום:

$$\text{פעולה על מטריצה} \;=\; \varphi \;\circ\; \text{פעולה על מערכת} \;\circ\; \varphi^{-1}$$

איפה $\varphi = $ `AugmentedMatrix`. תרגם למערכת, בצע שם, תרגם חזרה. **אפס הגדרות חדשות, אפס הוכחות חדשות.** כל המשפטים של 1.7 עובדים דרך התרגום.

זה עובד רק כי הוכחת ש‑$\varphi$ הפיכה. שני משפטי הרוֹנד־טריפ הם התנאי, לא קישוט.

וזה גם למה `applyMatrixSequence_append` היא הוכחה של ארבע שורות:

```lean
unfold applyMatrixSequence
rw [applySequence_append]
rw [systemFromAugmentedMatrix_AugmentedMatrix]
```

הטענה על מטריצות מתקפלת מיידית לטענה על מערכות (שכבר הוכחת), וה‑`systemFromAugmentedMatrix_AugmentedMatrix` מבטל את התרגום־הלוך־חזור באמצע.

## `inverseElementaryOperation`

```lean
noncomputable def inverseElementaryOperation : ElementaryOperation A m n → ElementaryOperation A m n
  | .switchRows i j       => .switchRows i j
  | .scaleRow i c hc      => .scaleRow i (inv c hc) (proof that inv c ≠ 0)
  | .addRow i j c hij     => .addRow i j (neg c) hij
```

### טריק 9 — ההופכית של פעולה אלמנטרית היא פעולה אלמנטרית

זו טענה מתמטית אמיתית, לא רק נוחות: הקבוצה של פעולות השורה **סגורה להיפוך**. החלפה היא הופכית לעצמה; כפל ב‑`c` מתהפך ע"י כפל ב‑`c⁻¹`; הוספת `c·Rⱼ` מתהפכת ע"י הוספת `(-c)·Rⱼ`.

וזה בדיוק המקום שבו טריק 6 (ההנחות בקונסטרוקטור) גובה מחיר וגם משלם: כדי לבנות את `.scaleRow i (inv c hc) _` אתה **חייב** לספק הוכחה ש‑`inv c ≠ 0`. הוכחת אותה בשורה, וזו הוכחה יפה:

> נניח `inv c = 0`. אז `c * inv c = c * 0 = 0`. אבל לפי `MulInverseCancel`, `c * inv c = 1`. אז `0 = 1`, בסתירה ל‑`Field_.zero_neq_one`.

`apply_inverseElementaryOperation` מוכיח שזה באמת עובד: `op⁻¹ (op sys) = sys`. שלושה מקרים, כל אחד עם `cases system | mk`, `congr 1` (כדי לרדת משוויון מבנים לשוויון שדות), `funext`, ו‑`by_cases` על "האם זו השורה שנגענו בה".

במקרה `addRow` הוצאת למה מקומית יפה:

```lean
have cancelTerm (x : A) : Field_.add (Field_.mul scalar x) (Field_.mul (neg scalar) x) = Field_.zero
```

כלומר $c\cdot x + (-c)\cdot x = 0$ — פילוג מימין, ואז $c + (-c) = 0$, ואז $0 \cdot x = 0$. הוצאת אותה החוצה כי היא נחוצה גם למקדמים וגם לאיבר החופשי. נכון.

## `applySequence_append` — ההוכחה הקשה בפרויקט

```lean
applySequence (a + b) (Fin.append f s) system = applySequence b s (applySequence a f system)
```

"להפעיל סדרה משורשרת = להפעיל את הראשונה ואז את השנייה." נשמע מובן מאליו, ולוקח 70 שורות — כי `Fin.append` מוגדרת דרך `Fin.addCases`, `Fin.castAdd` ו‑`Fin.natAdd`, וצריך להראות שהקיצוץ של המשורשרת שווה לשרשור עם המקוצצת (`prefixEquality`), ושהאיבר האחרון של המשורשרת הוא האיבר האחרון של השנייה (`lastEquality`).

זה לא סיבוך מיותר — זה המחיר של עבודה עם `Fin`. **למה נזקקת לזה בכלל:** `RowEquivalent_trans`. אם `M → N` דרך סדרה באורך `a` ו‑`N → P` דרך סדרה באורך `b`, צריך סדרה אחת באורך `a+b` שמוליכה `M → P`. בלי המשפט הזה אין טרנזיטיביות, ובלי טרנזיטיביות אין יחס שקילות.

## `RowEquivalent` והמשפטים עליו

```lean
def RowEquivalent (firstMatrix secondMatrix : Ntuple (Ntuple A (n + 1)) m) : Prop :=
  ∃ length : Nat, ∃ operations : Ntuple (ElementaryOperation A m n) length,
    secondMatrix = applyMatrixSequence length operations firstMatrix
```

זו הגדרה 1.8.1 בספר. שים לב שהאורך **קיים** ולא נתון — "יש סדרה סופית כלשהי".

| משפט | הרעיון |
|---|---|
| `RowEquivalent_refl` | הסדרה הריקה. `⟨0, Fin.elim0, _⟩` — `Fin.elim0` היא הפונקציה מ‑`Fin 0`, שקיימת כי אין מה להגדיר |
| `RowEquivalent_single` | סדרה באורך 1 |
| `RowEquivalent_trans` | `Fin.append` + `applyMatrixSequence_append`. כאן משתלמות 70 השורות |
| `RowEquivalent_inverse_step` | צעד אחד אחורה, דרך `inverseElementaryOperation` |
| `RowEquivalent_symm` | אינדוקציה על האורך, קילוף מהסוף |
| `RowEquivalent_equivalence` | `⟨refl, symm, trans⟩` |

### `RowEquivalent_symm` — קילוף מהסוף

זו ההוכחה שאני הכי אוהב שם. הרעיון:

אם $N$ מתקבלת מ‑$M$ ע"י $k+1$ פעולות, סמן ב‑$B$ את המצב אחרי $k$ הראשונות. אז:
- $N$ שקולת־שורה ל‑$B$ — צעד אחד אחורה, `RowEquivalent_inverse_step`.
- $B$ שקולת־שורה ל‑$M$ — הנחת האינדוקציה.
- טרנזיטיביות → $N$ שקולת־שורה ל‑$M$.

שים לב ש‑`subst secondMatrix` לפני האינדוקציה הוא מה שמאפשר את זה: הוא מחליף את `N` בביטוי המפורש, וכך `induction length` יכולה לגעת בו. (Lean גם מכליל אוטומטית את `operations`, כי הטיפוס שלה תלוי ב‑`length` — בדיוק העניין מטריק 7.)

### `Equivalence` — למה זה שווה משהו

```lean
theorem RowEquivalent_equivalence : Equivalence (@RowEquivalent A _ m n) :=
  ⟨RowEquivalent_refl, RowEquivalent_symm, RowEquivalent_trans⟩
```

`Equivalence` הוא מבנה של Mathlib. ברגע שיש לך אותו, אתה יכול לבנות `Setoid` ולעבור ל‑`Quotient` — כלומר לדבר על **מחלקות שקילות של מטריצות**. זה מה שיאפשר לנסח בהמשך "לכל מטריצה יש צורה קנונית **יחידה**" (פרק 1.11) כטענה על מנה, ולא כאוסף טענות.

---

# סיכום הטריקים

| # | הטריק | מה הוא חסך |
|---|---|---|
| 1 | מטריצה = `Ntuple (Ntuple A n) m`, לא טיפוס חדש | כל האלגברה של 1.3 חלה על שורות בחינם |
| 2 | `dite` להפקת ההוכחה מהתנאי | `Fin n` מתוך `Fin (n+1)` בלי casts ידניים |
| 3 | `m₁ ≠ m₂` ב‑`AreEquivalent` | יאפשר זריקת שורות מתאפסות בפרק 1.12 |
| 4 | למות חישוב עם `rfl` | `rw` מדויק במקום `unfold` שמלכלך |
| 5 | פעולה אלמנטרית כטיפוס אינדוקטיבי | אפשר לרשום, לאחסן, לעשות אינדוקציה, ולהפוך |
| 6 | הנחות בתוך הקונסטרוקטור | פעולה לא חוקית היא שגיאת טיפוסים; `elementaryOperation_equivalent` ב‑3 שורות |
| 7 | `∀ ops` אחרי הנקודתיים | הנחת האינדוקציה חלה על הסדרה המקוצצת |
| 8 | הצמדה דרך `AugmentedMatrix` | אפס פעולות שורה חדשות, אפס הוכחות חדשות ב‑1.8 |
| 9 | `inverseElementaryOperation` | סימטריה של `RowEquivalent` — וגם קיצור אפשרי ל‑1.7 |

---

# מה שכדאי לתקן

1. **המשפט החסר של 1.8.** הספר מסיים בעמ' 70 ב‑*"אם שתי מטריצות הן שקולות‑שורה, אז המערכות הלינאריות שהן מייצגות הן שקולות"*. בנית את כל המכונה ולא ניסחת את המסקנה. ארבע שורות, בקובץ ששלחתי.

2. **כיוון ⇐ בשלושת משפטי 1.7 מיותר.** הספר (עמ' 68) לא מבטל אגפים — הוא מפעיל את כיוון ⇒ על הפעולה ההפוכה. אתה כבר בנית את `inverseElementaryOperation`, רק בקובץ הבא. אם תעביר אותו ל‑1.7, כל שלושת הכיוונים ההפוכים מתקצרים ללמה כללית אחת (~40 שורות פחות).

3. **`replaceRow` מתה.** או שתשתמש בה כדי להגדיר את `scaleRow` ו‑`addRow`, או שתמחק.

4. **הקיצוץ הידני חוזר 6 פעמים.** `fun i => ops ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩` — תגדיר אותו פעם אחת (`Fin.init` או `i.castSucc`) והקוד יתקצר משמעותית.

5. **`AreEquivalent_symm` חסר.** יש `refl` ו‑`trans`, אין `symm`. שורה אחת, וכדאי גם `Equivalence` כמו שעשית ב‑1.8.
