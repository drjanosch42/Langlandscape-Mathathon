import Lean

/-!
# The `tf_id` and `tf_aux` attributes

Every primary declaration of the project carries `@[tf_id "<ID>"]`; plumbing that document B renders carries
`@[tf_aux "<ID>"]` (PLAN.md §1.2). An ID has the form `<vol>.<area>.<kind>:<slug>` with

* `vol ∈ {I, II, III, X}`,
* `area` a lowercase alphanumeric word starting with a letter (`haar`, `adele`, `dummy`, ...),
* `kind ∈ {def, thm, prop, lem, cor, hyp, ex}`,
* `slug` kebab-case: lowercase alphanumeric words joined by single hyphens.

The attributes validate the format and reject an ID that is already used (by any declaration visible in the
current environment) and a declaration that is already tagged. The tags are stored in the persistent
environment extension `GL2TF.Meta.tagExt`, which `tfaudit` reads from the imported environment.

Duplicates between two modules that do not import each other cannot be seen here; `tfaudit` reports them
(see `GL2TF.Meta.duplicateIds`).
-/

open Lean Elab

namespace GL2TF.Meta

/-- Which of the two attributes produced a tag. -/
inductive TagKind where
  /-- `@[tf_id "..."]`: a primary declaration (shared A/B item or hypothesis). -/
  | id
  /-- `@[tf_aux "..."]`: B-only plumbing. -/
  | aux
  deriving Inhabited, BEq, Repr

/-- The attribute name of a tag kind. -/
def TagKind.attrName : TagKind → String
  | .id => "tf_id"
  | .aux => "tf_aux"

/-- One tag: the tagged declaration, its ID and the attribute used. -/
structure TagEntry where
  /-- The tagged declaration. -/
  declName : Name
  /-- The stable ID `<vol>.<area>.<kind>:<slug>`. -/
  id : String
  /-- `tf_id` or `tf_aux`. -/
  kind : TagKind
  deriving Inhabited, BEq, Repr

/-- The parts of a well-formed ID. -/
structure ParsedId where
  /-- `I`, `II`, `III` or `X`. -/
  vol : String
  /-- The topic code. -/
  area : String
  /-- `def`, `thm`, `prop`, `lem`, `cor`, `hyp` or `ex`. -/
  kind : String
  /-- The kebab-case slug. -/
  slug : String
  deriving Inhabited, BEq, Repr

/-- The allowed volumes. -/
def validVols : List String := ["I", "II", "III", "X"]

/-- The allowed item kinds. -/
def validKinds : List String := ["def", "thm", "prop", "lem", "cor", "hyp", "ex"]

private def isLowerAlnum (c : Char) : Bool := c.isLower || c.isDigit

/-- `area`: nonempty, lowercase letters and digits, starting with a letter. -/
def isValidArea (s : String) : Bool :=
  match s.toList with
  | c :: cs => c.isLower && cs.all isLowerAlnum
  | [] => false

/-- `slug`: kebab-case, i.e. nonempty lowercase alphanumeric words joined by single hyphens. -/
def isValidSlug (s : String) : Bool :=
  let words := s.splitOn "-"
  words.all fun w => !w.isEmpty && w.toList.all isLowerAlnum

/-- Parse `<vol>.<area>.<kind>:<slug>`; `none` if the string is not a well-formed ID. -/
def parseId (s : String) : Option ParsedId :=
  match s.splitOn ":" with
  | [pre, slug] =>
    match pre.splitOn "." with
    | [vol, area, kind] =>
      if validVols.contains vol && isValidArea area && validKinds.contains kind && isValidSlug slug then
        some { vol, area, kind, slug }
      else none
    | _ => none
  | _ => none

/-- Whether `s` is a well-formed ID. -/
def isValidId (s : String) : Bool := (parseId s).isSome

/-- The state of `tagExt`: all tags visible in the environment, indexed by ID and by declaration. -/
structure TagState where
  /-- ID ↦ tag. -/
  byId : Std.HashMap String TagEntry := {}
  /-- Declaration ↦ tag. -/
  byDecl : Std.HashMap Name TagEntry := {}
  deriving Inhabited

/-- Add one tag to the state (later entries win; the attribute rejects duplicates before adding). -/
def TagState.insert (s : TagState) (e : TagEntry) : TagState :=
  { byId := s.byId.insert e.id e, byDecl := s.byDecl.insert e.declName e }

/-- The persistent environment extension holding every `tf_id`/`tf_aux` tag.

* `tagExt.getState env : TagState` covers the imported modules and the current one;
* `tagExt.getModuleEntries env i : Array TagEntry` gives the tags made in the `i`-th imported module. -/
initialize tagExt : SimplePersistentEnvExtension TagEntry TagState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := TagState.insert
    addImportedFn := fun arrs => arrs.foldl (fun s a => a.foldl TagState.insert s) {}
  }

/-- The tag of a declaration, if any. -/
def findTag? (env : Environment) (decl : Name) : Option TagEntry :=
  (tagExt.getState env).byDecl[decl]?

/-- The declaration carrying an ID, if any. -/
def findDeclById? (env : Environment) (id : String) : Option TagEntry :=
  (tagExt.getState env).byId[id]?

/-- All tags made in imported modules, with their module names, in import order. -/
def importedTagsByModule (env : Environment) : Array (Name × Array TagEntry) := Id.run do
  let mut out := #[]
  for h : i in [:env.header.moduleNames.size] do
    let es := tagExt.getModuleEntries env i
    unless es.isEmpty do
      out := out.push (env.header.moduleNames[i], es)
  return out

/-- All tags visible in `env`: those of imported modules followed by those of the current module.
This is the list `tfaudit` iterates over (it runs on an imported environment, where the second part is empty). -/
def allTags (env : Environment) : Array TagEntry :=
  (importedTagsByModule env).foldl (fun acc (_, es) => acc ++ es) #[] ++
    (tagExt.getEntries env).reverse.toArray

/-- IDs that occur more than once in `allTags env` (possible only across modules that do not import each other). -/
def duplicateIds (env : Environment) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut dups : Array String := #[]
  for e in allTags env do
    if seen.contains e.id then
      unless dups.contains e.id do dups := dups.push e.id
    else
      seen := seen.insert e.id
  return dups

/-- Validate and record a tag (shared code of both attributes). -/
def addTag (decl : Name) (id : String) (kind : TagKind) : AttrM Unit := do
  let env ← getEnv
  unless isValidId id do
    throwError "{kind.attrName}: malformed ID \"{id}\"; expected <vol>.<area>.<kind>:<slug> with \
      vol ∈ \{{", ".intercalate validVols}}, kind ∈ \{{", ".intercalate validKinds}}, \
      area lowercase alphanumeric, slug kebab-case"
  if let some e := findDeclById? env id then
    throwError "{kind.attrName}: ID \"{id}\" is already used by `{e.declName}` (@[{e.kind.attrName}]); \
      IDs are never reused"
  if let some e := findTag? env decl then
    throwError "{kind.attrName}: `{decl}` is already tagged @[{e.kind.attrName} \"{e.id}\"]; \
      one tag per declaration"
  modifyEnv (tagExt.addEntry · { declName := decl, id, kind })

/-- `@[tf_id "<vol>.<area>.<kind>:<slug>"]`: the stable ID of a primary declaration. -/
syntax (name := tfIdAttr) "tf_id " str : attr

/-- `@[tf_aux "<vol>.<area>.<kind>:<slug>"]`: the ID of a B-only item rendered as plumbing. -/
syntax (name := tfAuxAttr) "tf_aux " str : attr

initialize registerBuiltinAttribute {
  name := `tfIdAttr
  descr := "GL2TF stable ID of a primary declaration"
  add := fun decl stx attrKind => do
    unless attrKind == .global do throwError "tf_id must be global"
    match stx with
    | `(attr| tf_id $s:str) => addTag decl s.getString .id
    | _ => throwUnsupportedSyntax
  applicationTime := .afterTypeChecking
}

initialize registerBuiltinAttribute {
  name := `tfAuxAttr
  descr := "GL2TF stable ID of a B-only auxiliary declaration"
  add := fun decl stx attrKind => do
    unless attrKind == .global do throwError "tf_aux must be global"
    match stx with
    | `(attr| tf_aux $s:str) => addTag decl s.getString .aux
    | _ => throwUnsupportedSyntax
  applicationTime := .afterTypeChecking
}

end GL2TF.Meta
