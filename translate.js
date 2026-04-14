const DECORATOR_CLASSES = new Set([ "UICorner", "UIStroke", "UIGradient" ]);

const LAYOUT_CLASSES = new Set([ "UIListLayout", "UIGridLayout", "UIPageLayout", "UITableLayout", "UIPadding", "UIAspectRatioConstraint", "UISizeConstraint", "UITextSizeConstraint" ]);

const ROOT_GUI_CLASSES = new Set([ "ScreenGui", "BillboardGui", "SurfaceGui", "LayerCollector", "GuiMain" ]);

let liveModel = {
    nodes: new Map,
    roots: [],
    order: []
};

const SAMPLE = `local gui = Instance.new("ScreenGui")\ngui.Name = "Gui"\ngui.IgnoreGuiInset = true\n\nlocal frame = Instance.new("Frame")\nframe.Name = "Frame"\nframe.Size = UDim2.fromScale(0.45, 0.45)\nframe.Position = UDim2.fromScale(0.275, 0.275)\nframe.BackgroundColor3 = Color3.fromRGB(42, 46, 58)\nframe.BorderSizePixel = 0\nframe.Parent = gui\n`;

const input = document.getElementById("input");

const previewSurface = document.getElementById("previewSurface");

const errorBox = document.getElementById("error");

const runBtn = document.getElementById("runBtn");

const loadExampleBtn = document.getElementById("loadExampleBtn");

const downloadBtn = document.getElementById("downloadBtn");

const statusText = document.getElementById("statusText");

const propsEmpty = document.getElementById("propsEmpty");

const propsForm = document.getElementById("propsForm");

const propsClassReadout = document.getElementById("propsClassReadout");

const propsHierarchyReadout = document.getElementById("propsHierarchyReadout");

const propsApply = document.getElementById("propsApply");

const propsDelete = document.getElementById("propsDelete");

const propsLiveApply = document.getElementById("propsLiveApply");

let livePropsDebounce = null;

const TRIDENT_STORAGE_KEY = "trident.editor.v1";

let persistEditorTimer = null;

let selectedNodeIds = new Set;

let primarySelectedId = null;

const MAX_UNDO = 80;

const undoStack = [];

const redoStack = [];

let restoringHistory = false;

let dragState = null;

/** TextButton: wait for pointer movement before starting move (so double-click can edit text). */
let textButtonDragPending = null;

let textButtonEditEl = null;

let textButtonEditKeydownHandler = null;

let liveApplyingFromForm = false;

/** After drag/resize, Size/Position/Anchor in the model are authoritative; don't overwrite from props inputs until user edits layout fields (avoids float/fallback mismatch → "fat" jumps). Holds every node id that was moved/resized in the current gesture (multi-select). */
let guiLayoutLockedIds = new Set;

/** Live apply: merge Size/Position/Anchor from the form only after the user edits a layout field, or when they click Apply (not on every propsText / color keystroke). */
let propsFormLayoutFieldsTouched = false;

let propsFormForceFullFormMerge = false;

const PROPS_LAYOUT_FIELD_IDS = new Set([ "propsSizeX", "propsSizeY", "propsPosX", "propsPosY", "propsAx", "propsAy" ]);

/** True while `refreshPropertiesPanel` is writing inputs — ignore spurious input/change that would clear the layout lock. */
let suppressLayoutUnlockFromPropsRefresh = false;

let propsLayoutPanelSyncRaf = 0;

let pendingPropsLayoutNodeId = null;

const SNAP_GUIDE_PX = 6;

const expandedExplorerIds = new Set;

const CHROME_Z = "2147483000";

function elementBoxInSurface(el) {
    if (!previewSurface || !el) return {
        left: 0,
        top: 0,
        w: 0,
        h: 0
    };
    const sr = previewSurface.getBoundingClientRect();
    const er = el.getBoundingClientRect();
    return {
        left: er.left - sr.left,
        top: er.top - sr.top,
        w: er.width,
        h: er.height
    };
}

function parentPointToSurfaceX(parentEl, xInParent) {
    if (!previewSurface || !parentEl) return xInParent;
    const pr = parentEl.getBoundingClientRect();
    const sr = previewSurface.getBoundingClientRect();
    return pr.left - sr.left + xInParent;
}

function parentPointToSurfaceY(parentEl, yInParent) {
    if (!previewSurface || !parentEl) return yInParent;
    const pr = parentEl.getBoundingClientRect();
    const sr = previewSurface.getBoundingClientRect();
    return pr.top - sr.top + yInParent;
}

function ensureSnapLayer() {
    if (!previewSurface) return;
    let layer = previewSurface.querySelector("#tridentSnapLayer");
    if (!layer) {
        layer = document.createElement("div");
        layer.id = "tridentSnapLayer";
        layer.className = "trident-snap-layer";
        layer.setAttribute("aria-hidden", "true");
        previewSurface.appendChild(layer);
    }
}

function clearSnapGuides() {
    const layer = previewSurface?.querySelector("#tridentSnapLayer");
    if (layer) layer.innerHTML = "";
}

function renderSnapGuides(vxSurf, vySurf) {
    if (!previewSurface) return;
    ensureSnapLayer();
    const layer = previewSurface.querySelector("#tridentSnapLayer");
    if (!layer) return;
    layer.innerHTML = "";
    for (const x of vxSurf) {
        const ln = document.createElement("div");
        ln.className = "trident-snap-line-v";
        ln.style.left = `${Math.round(x)}px`;
        layer.appendChild(ln);
    }
    for (const y of vySurf) {
        const ln = document.createElement("div");
        ln.className = "trident-snap-line-h";
        ln.style.top = `${Math.round(y)}px`;
        layer.appendChild(ln);
    }
}

function snapMoveWithGuides(el, nl, nt, ew, eh) {
    const parent = el.offsetParent || previewSurface;
    const { w: prW, h: prH } = getParentUdimBasisPx(parent);
    const SNAP = SNAP_GUIDE_PX;
    const xTargets = new Set([ 0, prW * .5, prW ]);
    const yTargets = new Set([ 0, prH * .5, prH ]);
    const others = [ ...previewSurface.querySelectorAll(".roblox-ui") ].filter(n => n !== el && !n.classList.contains("trident-viewport") && n.offsetParent === parent);
    for (const o of others) {
        const ol = o.offsetLeft;
        const ot = o.offsetTop;
        const ow = o.offsetWidth;
        const oh = o.offsetHeight;
        xTargets.add(ol);
        xTargets.add(ol + ow * .5);
        xTargets.add(ol + ow);
        yTargets.add(ot);
        yTargets.add(ot + oh * .5);
        yTargets.add(ot + oh);
    }
    const xEdge = [ 0, ew * .5, ew ];
    const yEdge = [ 0, eh * .5, eh ];
    let bestNl = nl;
    let minDx = SNAP + 1;
    let guideX = null;
    for (const tx of xTargets) {
        for (const xe of xEdge) {
            const cand = tx - xe;
            const d = cand - nl;
            if (Math.abs(d) < minDx && Math.abs(d) <= SNAP) {
                minDx = Math.abs(d);
                bestNl = cand;
                guideX = tx;
            }
        }
    }
    let bestNt = nt;
    let minDy = SNAP + 1;
    let guideY = null;
    for (const ty of yTargets) {
        for (const ye of yEdge) {
            const cand = ty - ye;
            const d = cand - nt;
            if (Math.abs(d) < minDy && Math.abs(d) <= SNAP) {
                minDy = Math.abs(d);
                bestNt = cand;
                guideY = ty;
            }
        }
    }
    const vxSurf = [];
    const vySurf = [];
    if (guideX != null) vxSurf.push(parentPointToSurfaceX(parent, guideX));
    if (guideY != null) vySurf.push(parentPointToSurfaceY(parent, guideY));
    return {
        nl: bestNl,
        nt: bestNt,
        vxSurf: vxSurf,
        vySurf: vySurf
    };
}

function setStatus(text) {
    if (statusText) statusText.textContent = text == null ? "" : String(text);
}

function getEditorSnapshotJson() {
    return JSON.stringify(getEditorSnapshot());
}

function pushUndoState() {
    if (restoringHistory) return;
    undoStack.push(getEditorSnapshotJson());
    if (undoStack.length > MAX_UNDO) undoStack.shift();
    redoStack.length = 0;
}

function performUndo() {
    if (undoStack.length === 0) return;
    restoringHistory = true;
    try {
        const prev = JSON.parse(undoStack.pop());
        redoStack.push(getEditorSnapshotJson());
        applyEditorSnapshot(prev);
        render();
        setStatus("Undone");
    } finally {
        restoringHistory = false;
    }
}

function performRedo() {
    if (redoStack.length === 0) return;
    restoringHistory = true;
    try {
        const next = JSON.parse(redoStack.pop());
        undoStack.push(getEditorSnapshotJson());
        applyEditorSnapshot(next);
        render();
        setStatus("Redone");
    } finally {
        restoringHistory = false;
    }
}

function getPrimarySelectedId() {
    if (primarySelectedId && selectedNodeIds.has(primarySelectedId)) return primarySelectedId;
    const first = selectedNodeIds.values().next().value;
    return first ?? null;
}

function setSelectionSingle(id) {
    selectedNodeIds.clear();
    if (id) {
        selectedNodeIds.add(id);
        primarySelectedId = id;
    } else primarySelectedId = null;
}

function selectWithModifiers(id, opts) {
    const { additive, toggle } = opts || {};
    if (!liveModel?.nodes?.has(id)) return;
    if (toggle) {
        if (selectedNodeIds.has(id)) {
            selectedNodeIds.delete(id);
            if (primarySelectedId === id) primarySelectedId = getPrimarySelectedId();
        } else {
            selectedNodeIds.add(id);
            primarySelectedId = id;
        }
    } else if (additive) {
        selectedNodeIds.add(id);
        primarySelectedId = id;
    } else {
        setSelectionSingle(id);
    }
}

function sanitizeSelectionAfterModelChange() {
    for (const sid of [ ...selectedNodeIds ]) {
        if (!liveModel?.nodes?.has(sid)) selectedNodeIds.delete(sid);
    }
    if (primarySelectedId && !selectedNodeIds.has(primarySelectedId)) primarySelectedId = getPrimarySelectedId();
}

function getTopLevelSelectionIds() {
    const ids = [ ...selectedNodeIds ].filter(id => liveModel?.nodes?.has(id));
    const top = [];
    for (const id of ids) {
        let p = parentVarFor(id, liveModel.nodes);
        let underOther = false;
        while (p) {
            if (selectedNodeIds.has(p)) {
                underOther = true;
                break;
            }
            p = parentVarFor(p, liveModel.nodes);
        }
        if (!underOther) top.push(id);
    }
    return top;
}

function selectionHasUniformClass() {
    const ids = [ ...selectedNodeIds ].filter(id => liveModel?.nodes?.has(id));
    if (ids.length === 0) return true;
    const c0 = liveModel.nodes.get(ids[0]).className;
    return ids.every(id => liveModel.nodes.get(id).className === c0);
}

function stripBlockComments(s) {
    let out = "";
    let i = 0;
    const n = s.length;
    while (i < n) {
        if (s.slice(i, i + 4) === "--[[") {
            i += 4;
            const end = s.indexOf("]]", i);
            i = end === -1 ? n : end + 2;
            continue;
        }
        out += s[i];
        i++;
    }
    return out;
}

function stripLineCommentsOutsideStrings(line) {
    let inStr = false;
    let q = "";
    for (let i = 0; i < line.length; i++) {
        const c = line[i];
        if (!inStr && (c === '"' || c === "'")) {
            inStr = true;
            q = c;
            continue;
        }
        if (inStr) {
            if (c === q && line[i - 1] !== "\\") inStr = false;
            continue;
        }
        if (c === "-" && line[i + 1] === "-") return line.slice(0, i).trimEnd();
    }
    return line;
}

function normalizeSource(src) {
    let s = String(src).replace(/\r\n/g, "\n").replace(/\r/g, "\n");
    s = stripBlockComments(s);
    const lines = s.split("\n");
    const kept = lines.map(line => stripLineCommentsOutsideStrings(line)).filter(l => l.trim().length > 0);
    return kept.join("\n");
}

/** Parsed from raw source before comments are stripped; keeps Input-drag export across Refresh. */
function extractTridentInputDragPragmas(source) {
    const out = new Map;
    const re = /^\s*--\s*TRIDENT:InputDrag:([A-Za-z_]\w*)\s*$/gm;
    let m;
    while ((m = re.exec(String(source || ""))) !== null) {
        out.set(m[1], true);
    }
    return out;
}

function emitInputDragLuauLines(varName) {
    const v = varName;
    return [ `-- TRIDENT:InputDrag:${v}`, `local ${v}_dragging, ${v}_dragInput, ${v}_dragStart, ${v}_startPos`, `local function ${v}_updateDrag(input)`, `    local delta = input.Position - ${v}_dragStart`, `    ${v}.Position = UDim2.new(${v}_startPos.X.Scale, ${v}_startPos.X.Offset + delta.X, ${v}_startPos.Y.Scale, ${v}_startPos.Y.Offset + delta.Y)`, `end`, `${v}.InputBegan:Connect(function(input)`, `    if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then`, `        ${v}_dragging = true`, `        ${v}_dragStart = input.Position`, `        ${v}_startPos = ${v}.Position`, `        input.Changed:Connect(function()`, `            if input.UserInputState == Enum.UserInputState.End then`, `                ${v}_dragging = false`, `            end`, `        end)`, `    end`, `end)`, `${v}.InputChanged:Connect(function(input)`, `    if input.UserInputType == Enum.UserInputType.MouseMovement or input.UserInputType == Enum.UserInputType.Touch then`, `        ${v}_dragInput = input`, `    end`, `end)`, `UserInputService.InputChanged:Connect(function(input)`, `    if input == ${v}_dragInput and ${v}_dragging then`, `        ${v}_updateDrag(input)`, `    end`, `end)` ];
}

function splitStatements(s) {
    const statements = [];
    let buf = "";
    let depth = 0;
    let inStr = false;
    let q = "";
    const pushBuf = () => {
        const t = buf.trim();
        if (t) statements.push(t);
        buf = "";
    };
    for (let i = 0; i < s.length; i++) {
        const c = s[i];
        if (!inStr && (c === '"' || c === "'")) {
            inStr = true;
            q = c;
            buf += c;
            continue;
        }
        if (inStr) {
            buf += c;
            if (c === q && s[i - 1] !== "\\") inStr = false;
            continue;
        }
        if (c === "{") depth++;
        if (c === "}") depth--;
        buf += c;
        if (c === "\n" && depth === 0) pushBuf();
    }
    pushBuf();
    return statements;
}

function parseLuau(source) {
    const nodes = new Map;
    const roots = [];
    const parentById = new Map;
    const childrenById = new Map;
    const order = [];
    if (!String(source || "").trim()) {
        return {
            nodes: nodes,
            roots: roots,
            order: order
        };
    }
    const normalized = normalizeSource(source);
    const statements = splitStatements(normalized);
    for (const stmt of statements) {
        const oneLine = stmt.replace(/\s+/g, " ").trim();
        let m = stmt.match(/^local\s+([A-Za-z_]\w*)\s*=\s*Instance\.new\(["']([A-Za-z_]\w*)["']\)\s*$/);
        if (m) {
            const [, id, className] = m;
            if (!nodes.has(id)) {
                nodes.set(id, {
                    id: id,
                    varName: id,
                    className: className,
                    props: {},
                    children: []
                });
                order.push(id);
            } else {
                nodes.get(id).className = className;
            }
            continue;
        }
        m = stmt.match(/^([A-Za-z_]\w*)\.Parent\s*=\s*([A-Za-z_]\w*)\s*$/);
        if (m) {
            const [, childId, parentId] = m;
            parentById.set(childId, parentId);
            if (!childrenById.has(parentId)) childrenById.set(parentId, []);
            if (!childrenById.get(parentId).includes(childId)) childrenById.get(parentId).push(childId);
            continue;
        }
        m = stmt.match(/^([A-Za-z_]\w*)\.([A-Za-z_]\w*)\s*=\s*([\s\S]+)$/);
        if (m) {
            const [, id, prop, rawRhs] = m;
            if (!nodes.has(id)) continue;
            nodes.get(id).props[prop] = parseValue(rawRhs.trim());
            continue;
        }
    }
    for (const [id, node] of nodes) {
        node.children = childrenById.has(id) ? [ ...childrenById.get(id) ] : [];
        if (!parentById.has(id)) roots.push(id);
    }
    for (const [, node] of nodes) {
        if (node.className === "ScreenGui") migrateScreenGuiNodeProps(node.props);
    }
    const dragPragmas = extractTridentInputDragPragmas(source);
    for (const [vn] of dragPragmas) {
        if (nodes.has(vn)) {
            nodes.get(vn).props.TridentInputDrag = true;
        }
    }
    return {
        nodes: nodes,
        roots: roots,
        order: order
    };
}

function parseValue(raw) {
    const s = raw.replace(/\s+/g, " ").trim();
    if (/^["'].*["']$/.test(s)) return s.slice(1, -1);
    if (/^-?\d+(\.\d+)?$/.test(s)) return Number(s);
    if (s === "true") return true;
    if (s === "false") return false;
    let m = s.match(/^Color3\.fromRGB\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)$/);
    if (m) return {
        type: "color3",
        r: Number(m[1]),
        g: Number(m[2]),
        b: Number(m[3])
    };
    m = s.match(/^Color3\.fromHex\(\s*["']#?([0-9a-fA-F]{6})["']\s*\)$/);
    if (m) {
        const hex = m[1];
        return {
            type: "color3",
            r: parseInt(hex.slice(0, 2), 16),
            g: parseInt(hex.slice(2, 4), 16),
            b: parseInt(hex.slice(4, 6), 16)
        };
    }
    m = s.match(/^UDim2\.fromScale\(\s*([-\d.]+)\s*,\s*([-\d.]+)\s*\)$/);
    if (m) return {
        type: "udim2",
        xScale: Number(m[1]),
        xOffset: 0,
        yScale: Number(m[2]),
        yOffset: 0
    };
    m = s.match(/^UDim2\.fromOffset\(\s*([-\d.]+)\s*,\s*([-\d.]+)\s*\)$/);
    if (m) return {
        type: "udim2",
        xScale: 0,
        xOffset: Number(m[1]),
        yScale: 0,
        yOffset: Number(m[2])
    };
    m = s.match(/^UDim2\.new\(\s*([-\d.]+)\s*,\s*([-\d.]+)\s*,\s*([-\d.]+)\s*,\s*([-\d.]+)\s*\)$/);
    if (m) {
        return {
            type: "udim2",
            xScale: Number(m[1]),
            xOffset: Number(m[2]),
            yScale: Number(m[3]),
            yOffset: Number(m[4])
        };
    }
    m = s.match(/^UDim\.new\(\s*([-\d.]+)\s*,\s*([-\d.]+)\s*\)$/);
    if (m) return {
        type: "udim",
        scale: Number(m[1]),
        offset: Number(m[2])
    };
    m = s.match(/^Vector2\.new\(\s*([-\d.]+)\s*,\s*([-\d.]+)\s*\)$/);
    if (m) return {
        type: "vector2",
        x: Number(m[1]),
        y: Number(m[2])
    };
    m = s.match(/^Enum\.(.+)$/);
    if (m) return {
        type: "enumPath",
        path: m[1].trim()
    };
    const cs = parseColorSequence(raw);
    if (cs) return {
        type: "colorSequence",
        keypoints: cs
    };
    return {
        type: "raw",
        value: raw
    };
}

function parseColorSequence(raw) {
    const keypoints = [];
    const re = /ColorSequenceKeypoint\.new\(\s*([-.\d]+)\s*,\s*Color3\.fromRGB\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)\s*\)/g;
    let m;
    while ((m = re.exec(raw)) !== null) {
        keypoints.push({
            time: Number(m[1]),
            color: [ Number(m[2]), Number(m[3]), Number(m[4]) ]
        });
    }
    return keypoints.length ? keypoints : null;
}

function buildHtmlTree(id, nodes, parentEl, isRootViewport) {
    const node = nodes.get(id);
    if (!node) return null;
    if (DECORATOR_CLASSES.has(node.className) || LAYOUT_CLASSES.has(node.className)) return null;
    const el = createElementForClass(node.className);
    el.classList.add("roblox-ui");
    el.dataset.nodeId = node.id;
    el.dataset.className = node.className;
    el.tabIndex = 0;
    const parentIsSurface = parentEl === previewSurface || parentEl.classList?.contains("trident-root-wrap") || parentEl.classList?.contains("trident-viewport");
    if (node.className === "ScreenGui" || isRootViewport && ROOT_GUI_CLASSES.has(node.className)) {
        el.classList.add("trident-viewport");
        el.style.position = "absolute";
        el.style.left = "0";
        el.style.top = "0";
        el.style.width = "100%";
        el.style.height = "100%";
        el.style.overflow = "visible";
        applyGuiObjectStyles(el, node.props, parentEl, true);
        if (!el._tridentComputedW || !el._tridentComputedH) {
            const ps = previewSurface;
            el._tridentComputedW = ps?.clientWidth || 800;
            el._tridentComputedH = ps?.clientHeight || 600;
        }
    } else {
        applyGuiObjectStyles(el, node.props, parentEl, parentIsSurface);
    }
    applyLayoutAndPaddingToElement(el, node, nodes);
    const decorators = collectDecorators(node, nodes);
    applyDecorators(el, decorators, nodes);
    for (const childId of sortedRenderableChildIds(node, nodes)) {
        const cn = nodes.get(childId);
        if (!cn) continue;
        const childEl = buildHtmlTree(childId, nodes, el, false);
        if (childEl) el.appendChild(childEl);
    }
    return el;
}

function collectDecorators(node, nodes) {
    return node.children.map(cid => nodes.get(cid)).filter(c => c && DECORATOR_CLASSES.has(c.className));
}

function sortedRenderableChildIds(node, nodes) {
    const rows = [];
    node.children.forEach((cid, orderIdx) => {
        const cn = nodes.get(cid);
        if (!cn) return;
        if (DECORATOR_CLASSES.has(cn.className) || LAYOUT_CLASSES.has(cn.className)) return;
        const z = layerSortKeyForRenderableChild(cn);
        rows.push({
            cid: cid,
            z: z,
            orderIdx: orderIdx
        });
    });
    rows.sort((a, b) => a.z !== b.z ? a.z - b.z : a.orderIdx - b.orderIdx);
    return rows.map(r => r.cid);
}

function normalizeGuiZIndex(props) {
    if (typeof props?.ZIndex === "number" && Number.isFinite(props.ZIndex)) {
        return Math.max(-32768, Math.min(32767, Math.round(props.ZIndex)));
    }
    return 1;
}

/** ScreenGui uses DisplayOrder, not ZIndex (ZIndex is invalid on ScreenGui in Roblox). */
function migrateScreenGuiNodeProps(props) {
    if (!props || typeof props !== "object") return;
    const dp = props.DisplayOrder;
    const zp = props.ZIndex;
    const hasDo = typeof dp === "number" && Number.isFinite(dp);
    if (!hasDo && typeof zp === "number" && Number.isFinite(zp)) {
        props.DisplayOrder = Math.max(0, Math.min(2147483647, Math.round(zp)));
    }
    if ("ZIndex" in props) delete props.ZIndex;
}

function layerSortKeyForRenderableChild(node) {
    if (!node) return 1;
    const p = node.props || {};
    if (node.className === "ScreenGui") {
        if (typeof p.DisplayOrder === "number" && Number.isFinite(p.DisplayOrder)) {
            return Math.max(0, Math.min(2147483647, Math.round(p.DisplayOrder)));
        }
        if (typeof p.ZIndex === "number" && Number.isFinite(p.ZIndex)) {
            return Math.max(0, Math.min(2147483647, Math.round(p.ZIndex)));
        }
        return 1;
    }
    if (typeof p.ZIndex === "number" && Number.isFinite(p.ZIndex)) return Math.round(p.ZIndex);
    return 1;
}

function zIndexForSelectionChrome() {
    return CHROME_Z;
}

function createElementForClass(className) {
    switch (className) {
      case "TextButton":
        {
            const b = document.createElement("button");
            b.type = "button";
            return b;
        }

      case "ImageButton":
        {
            const ib = document.createElement("button");
            ib.type = "button";
            return ib;
        }

      case "TextBox":
        return document.createElement("textarea");

      case "ImageLabel":
      case "VideoFrame":
        return document.createElement("div");

      default:
        return document.createElement("div");
    }
}

function applyGuiObjectStyles(el, props, parentEl, fillParent) {
    const { w: pw, h: ph } = getParentUdimBasisPx(parentEl);
    el.style.position = "absolute";
    el.style.boxSizing = "border-box";
    el.style.transform = "none";
    const ax = props.AnchorPoint && props.AnchorPoint.type === "vector2" ? props.AnchorPoint.x : 0;
    const ay = props.AnchorPoint && props.AnchorPoint.type === "vector2" ? props.AnchorPoint.y : 0;
    let wPx = 120;
    let hPx = 40;
    const size = props.Size;
    if (size && size.type === "udim2") {
        wPx = udim2AxisPixels(size.xScale, size.xOffset, pw);
        hPx = udim2AxisPixels(size.yScale, size.yOffset, ph);
        el.style.width = `${Math.round(wPx)}px`;
        el.style.height = `${Math.round(hPx)}px`;
    } else if (!fillParent) {
        el.style.width = `${wPx}px`;
        el.style.height = `${hPx}px`;
    } else if (fillParent) {
        wPx = pw;
        hPx = ph;
    }
    el._tridentComputedW = wPx;
    el._tridentComputedH = hPx;
    const pos = props.Position;
    if (pos && pos.type === "udim2") {
        const px = udim2AxisPixels(pos.xScale, pos.xOffset, pw);
        const py = udim2AxisPixels(pos.yScale, pos.yOffset, ph);
        const leftPx = px - ax * wPx;
        const topPx = py - ay * hPx;
        el.style.left = `${Math.round(leftPx)}px`;
        el.style.top = `${Math.round(topPx)}px`;
    } else if (!fillParent) {
        el.style.left = "0px";
        el.style.top = "0px";
    }
    const cn = el.dataset.className;
    if (cn === "ScreenGui") {
        const legacyZ = typeof props.ZIndex === "number" && Number.isFinite(props.ZIndex) ? props.ZIndex : null;
        const d = typeof props.DisplayOrder === "number" && Number.isFinite(props.DisplayOrder) ? props.DisplayOrder : legacyZ != null ? legacyZ : 1;
        el.style.zIndex = String(Math.max(0, Math.min(2147483647, Math.round(d))));
    } else {
        el.style.zIndex = String(normalizeGuiZIndex(props));
    }
    const isText = el.tagName === "BUTTON" || el.tagName === "TEXTAREA" || [ "TextLabel", "TextButton", "TextBox" ].includes(el.dataset.className);
    const textGui = [ "TextLabel", "TextButton", "TextBox" ].includes(cn);
    const imageGui = cn === "ImageLabel" || cn === "ImageButton";
    const bt = typeof props.BackgroundTransparency === "number" ? Math.min(1, Math.max(0, props.BackgroundTransparency)) : 0;
    if (props.BackgroundColor3 && props.BackgroundColor3.type === "color3") {
        const c = props.BackgroundColor3;
        if (textGui || imageGui) {
            el.style.backgroundColor = `rgba(${c.r}, ${c.g}, ${c.b}, ${Math.max(0, 1 - bt)})`;
        } else {
            el.style.backgroundColor = color3ToCss(props.BackgroundColor3);
        }
    } else if (!isText || cn === "Frame" || cn === "ScrollingFrame") {
        if (bt >= 1) {
            el.style.backgroundColor = "transparent";
        } else {
            el.style.backgroundColor = "rgba(30,34,44,0.85)";
        }
    }
    if (typeof props.BackgroundTransparency === "number") {
        if (textGui || imageGui) {
            el.style.opacity = "1";
        } else {
            el.style.opacity = String(Math.max(.05, 1 - bt));
        }
    } else {
        el.style.opacity = "";
    }
    if (typeof props.BorderSizePixel === "number" && props.BorderSizePixel > 0) {
        el.style.border = `${props.BorderSizePixel}px solid rgba(255,255,255,0.15)`;
    } else {
        el.style.border = "none";
    }
    if (textGui && typeof props.Text === "string") {
        const skipTextOverwrite = cn === "TextButton" && el.classList.contains("trident-tb-inline-edit") && document.activeElement === el;
        if (!skipTextOverwrite) {
            el.textContent = props.Text;
        }
        const tx = props.TextXAlignment?.type === "enumPath" ? props.TextXAlignment.path : "";
        const ty = props.TextYAlignment?.type === "enumPath" ? props.TextYAlignment.path : "";
        if (el.tagName === "TEXTAREA") {
            el.style.display = "block";
            el.style.padding = "6px";
            el.style.fontWeight = "600";
            el.style.fontFamily = "Gotham, Inter, sans-serif";
        } else {
            el.style.display = "flex";
            el.style.alignItems = mapTextYAlign(ty);
            el.style.justifyContent = mapTextXAlign(tx);
            el.style.textAlign = tx.endsWith("Left") ? "left" : tx.endsWith("Right") ? "right" : "center";
            el.style.padding = "6px";
            el.style.fontWeight = "600";
            el.style.fontFamily = "Gotham, Inter, sans-serif";
            el.style.overflow = "hidden";
            el.style.minWidth = "0";
            el.style.minHeight = "0";
        }
    }
    if (props.TextColor3 && props.TextColor3.type === "color3") {
        el.style.color = color3ToCss(props.TextColor3);
    }
    if (props.TextSize && typeof props.TextSize === "number") {
        el.style.fontSize = `${props.TextSize}px`;
        el.style.containerType = "";
    } else if (props.TextScaled === true) {
        const m = Math.max(1, Math.min(wPx, hPx));
        el.style.fontSize = `clamp(11px, ${0.022 * m}px, 22px)`;
        el.style.containerType = "";
    } else {
        el.style.fontSize = "14px";
        el.style.containerType = "";
    }
    if (props.TextWrapped === true && el.tagName !== "TEXTAREA") {
        el.style.whiteSpace = "normal";
        el.style.wordBreak = "break-word";
    }
    if (cn === "ScrollingFrame") {
        el.style.overflow = "auto";
        el.style.touchAction = "auto";
        const cs = props.CanvasSize;
        if (cs && cs.type === "udim2") {
            const cw = udim2AxisPixels(cs.xScale, cs.xOffset, pw);
            const ch = udim2AxisPixels(cs.yScale, cs.yOffset, ph);
            el.style.minHeight = `${Math.max(40, ch)}px`;
        }
        const st = props.ScrollBarThickness;
        if (typeof st === "number") {
            el.style.scrollbarWidth = st > 6 ? "auto" : "thin";
        }
    }
    if (cn === "ImageLabel" || cn === "ImageButton") {
        const img = typeof props.Image === "string" ? props.Image : "";
        el.style.backgroundSize = mapScaleType(props.ScaleType);
        el.style.backgroundPosition = "center";
        el.style.backgroundRepeat = "no-repeat";
        el.style.cursor = cn === "ImageButton" ? "pointer" : "default";
        applyImagePreview(el, img);
    }
    if (cn === "CanvasGroup" && typeof props.GroupTransparency === "number") {
        el.style.opacity = String(Math.max(0, 1 - props.GroupTransparency));
    }
    if (cn === "VideoFrame") {
        el.style.background = "repeating-linear-gradient(45deg,#222,#1a1a1a 8px)";
        el.innerHTML = '<span style="position:absolute;inset:0;display:flex;align-items:center;justify-content:center;font-size:12px;color:#888;">VideoFrame</span>';
    }
    if (cn === "ViewportFrame") {
        el.style.background = "#1e2130";
        el.innerHTML = '<span style="position:absolute;inset:0;display:flex;align-items:center;justify-content:center;font-size:11px;color:#6a7394;">ViewportFrame</span>';
    }
    if (supportsAutoUICorner(cn)) {
        const cr = props.CornerRadius;
        if (cr && cr.type === "udim" && typeof cr.offset === "number" && cr.offset > 0) {
            el.style.borderRadius = `${Math.min(64, cr.offset)}px`;
        } else {
            el.style.borderRadius = "";
        }
    }
    if (!fillParent && cn !== "ScreenGui" && cn !== "ScrollingFrame" && !el.classList.contains("trident-tb-inline-edit")) {
        el.style.touchAction = "none";
    }
}

function robloxImageUrlCandidates(assetId) {
    const id = String(assetId).replace(/\D/g, "");
    if (!id) return [];
    return [ `https://thumbnails.roblox.com/v1/assets?assetIds=${encodeURIComponent(id)}&size=420x420&format=Png&returnPolicy=PlaceHolder`, `https://assetdelivery.roblox.com/v1/asset?id=${encodeURIComponent(id)}`, `https://www.roblox.com/asset-thumbnail/image?assetId=${encodeURIComponent(id)}&width=420&height=420&format=png` ];
}

function imagePreviewUrlList(imageProp) {
    const s = String(imageProp || "").trim();
    if (!s) return [];
    let m = s.match(/rbxassetid:\/\/(\d+)/i);
    if (m) return robloxImageUrlCandidates(m[1]);
    m = s.match(/rbxthumb:\/\/[^\s"']*[?&]id=(\d+)/i);
    if (m) return robloxImageUrlCandidates(m[1]);
    if (/^https?:\/\//i.test(s)) return [ s ];
    return [];
}

function applyImagePreview(el, imageProp) {
    el.classList.remove("trident-image-placeholder");
    el.style.backgroundImage = "none";
    el.removeAttribute("data-image-hint");
    const raw = String(imageProp || "").trim();
    el.title = raw ? `Image: ${raw}` : "ImageLabel / ImageButton";
    const urls = imagePreviewUrlList(raw);
    if (!urls.length) {
        if (raw) {
            el.classList.add("trident-image-placeholder");
            el.dataset.imageHint = raw.length > 24 ? `${raw.slice(0, 22)}…` : raw;
        }
        return;
    }
    let idx = 0;
    const tryNext = () => {
        if (!el.isConnected) return;
        if (idx >= urls.length) {
            el.style.backgroundImage = "none";
            el.classList.add("trident-image-placeholder");
            el.dataset.imageHint = "Image preview unavailable";
            return;
        }
        const url = urls[idx++];
        const probe = new Image;
        probe.crossOrigin = "anonymous";
        probe.onload = () => {
            if (!el.isConnected) return;
            el.style.backgroundImage = `url(${JSON.stringify(url)})`;
            el.classList.remove("trident-image-placeholder");
            el.removeAttribute("data-image-hint");
        };
        probe.onerror = tryNext;
        probe.referrerPolicy = "no-referrer";
        probe.src = url;
    };
    tryNext();
}

function mapScaleType(enumVal) {
    if (!enumVal || enumVal.type !== "enumPath") return "contain";
    const p = enumVal.path || "";
    if (p.endsWith("Stretch")) return "100% 100%";
    if (p.endsWith("Crop")) return "cover";
    return "contain";
}

function mapTextXAlign(path) {
    if (!path) return "center";
    if (path.endsWith("Left")) return "flex-start";
    if (path.endsWith("Right")) return "flex-end";
    return "center";
}

function mapTextYAlign(path) {
    if (!path) return "center";
    if (path.endsWith("Top")) return "flex-start";
    if (path.endsWith("Bottom")) return "flex-end";
    return "center";
}

function enumPathSuffix(ep, fallback) {
    if (!ep || ep.type !== "enumPath" || !ep.path) return fallback;
    const last = String(ep.path).split(".").pop();
    return last || fallback;
}

function applyLayoutAndPaddingToElement(el, node, nodes) {
    for (const cid of node.children) {
        const ln = nodes.get(cid);
        if (!ln) continue;
        const p = ln.props;
        switch (ln.className) {
          case "UIListLayout":
            applyUIListLayout(el, p);
            break;

          case "UIPadding":
            applyUIPadding(el, p, el.clientWidth || 400, el.clientHeight || 400);
            break;

          case "UIGridLayout":
            applyUIGridLayout(el, p);
            break;

          case "UIPageLayout":
            el.style.overflow = "hidden";
            el.style.display = "flex";
            el.style.flexDirection = "row";
            break;

          case "UITableLayout":
            el.style.display = "table";
            break;

          case "UIAspectRatioConstraint":
            {
                const r = p.AspectRatio;
                if (typeof r === "number") el.style.aspectRatio = String(r);
                break;
            }

          case "UISizeConstraint":
            {
                const minS = p.MinSize;
                const maxS = p.MaxSize;
                if (minS && minS.type === "vector2") {
                    el.style.minWidth = `${minS.x}px`;
                    el.style.minHeight = `${minS.y}px`;
                }
                if (maxS && maxS.type === "vector2") {
                    el.style.maxWidth = `${maxS.x}px`;
                    el.style.maxHeight = `${maxS.y}px`;
                }
                break;
            }

          case "UITextSizeConstraint":
            {
                const minT = p.Min;
                const maxT = p.Max;
                if (typeof minT === "number" && typeof maxT === "number") {
                    el.style.fontSize = `clamp(${minT}px, 2cqmin, ${maxT}px)`;
                }
                break;
            }

          default:
            break;
        }
    }
}

function applyUIGridLayout(el, p) {
    el.style.display = "grid";
    const cs = p.CellSize;
    if (cs && cs.type === "udim2") {
        const w = cs.xOffset || Math.round((cs.xScale || 0) * 400);
        const h = cs.yOffset || Math.round((cs.yScale || 0) * 400);
        el.style.gridTemplateColumns = `repeat(auto-fill, ${Math.max(24, w)}px)`;
        el.style.gridAutoRows = `${Math.max(24, h)}px`;
    }
    const cp = p.CellPadding;
    if (cp && cp.type === "udim") {
        const gap = cp.offset + (cp.scale || 0) * 200;
        el.style.gap = `${Math.round(gap)}px`;
    }
}

function applyUIListLayout(el, p) {
    el.style.display = "flex";
    const fd = p.FillDirection;
    if (fd && fd.type === "enumPath" && fd.path && fd.path.includes("Horizontal")) {
        el.style.flexDirection = "row";
        el.style.flexWrap = "nowrap";
    } else {
        el.style.flexDirection = "column";
    }
    const ha = p.HorizontalAlignment;
    const va = p.VerticalAlignment;
    if (ha && ha.type === "enumPath" && ha.path) {
        if (ha.path.endsWith("Left")) el.style.alignItems = "flex-start";
        if (ha.path.endsWith("Center")) el.style.alignItems = "center";
        if (ha.path.endsWith("Right")) el.style.alignItems = "flex-end";
    }
    if (va && va.type === "enumPath" && va.path) {
        if (va.path.endsWith("Top")) el.style.justifyContent = "flex-start";
        if (va.path.endsWith("Center")) el.style.justifyContent = "center";
        if (va.path.endsWith("Bottom")) el.style.justifyContent = "flex-end";
    }
    const pad = p.Padding;
    if (pad && pad.type === "udim") {
        const px = pad.offset + (pad.scale || 0) * (el.clientWidth || 200);
        el.style.gap = `${Math.round(px)}px`;
    }
}

function applyUIPadding(el, p, pw, ph) {
    const mapPad = ud => {
        if (!ud || ud.type !== "udim") return 0;
        return Math.round(ud.offset + (ud.scale || 0) * Math.min(pw, ph));
    };
    el.style.paddingTop = `${mapPad(p.PaddingTop)}px`;
    el.style.paddingBottom = `${mapPad(p.PaddingBottom)}px`;
    el.style.paddingLeft = `${mapPad(p.PaddingLeft)}px`;
    el.style.paddingRight = `${mapPad(p.PaddingRight)}px`;
}

function applyDecorators(el, decorators, nodeMap) {
    for (const deco of decorators) {
        const p = deco.props;
        if (deco.className === "UICorner" && p.CornerRadius && p.CornerRadius.type === "udim") {
            const u = p.CornerRadius;
            el.style.borderRadius = u.offset > 0 ? `${Math.min(64, u.offset)}px` : `${Math.round(u.scale * 50)}%`;
        }
        if (deco.className === "UIStroke") {
            const th = typeof p.Thickness === "number" ? p.Thickness : 1;
            const col = p.Color && p.Color.type === "color3" ? color3ToCss(p.Color) : "rgba(255,255,255,0.3)";
            const tr = typeof p.Transparency === "number" ? p.Transparency : 0;
            const a = Math.max(0, 1 - tr);
            el.style.boxShadow = `inset 0 0 0 ${th}px ${toAlphaColor(col, a)}`;
        }
        if (deco.className === "UIGradient" && p.Color && p.Color.type === "colorSequence") {
            const rot = typeof p.Rotation === "number" ? p.Rotation : 0;
            const stops = p.Color.keypoints.sort((x, y) => x.time - y.time).map(k => `rgb(${k.color[0]}, ${k.color[1]}, ${k.color[2]}) ${k.time * 100}%`).join(", ");
            el.style.background = `linear-gradient(${rot}deg, ${stops})`;
        }
    }
}

function color3ToCss(c) {
    return `rgb(${c.r}, ${c.g}, ${c.b})`;
}

function udim2AxisToCss(scale, offset, parentSize) {
    return `${Math.round((scale || 0) * parentSize + (offset || 0))}px`;
}

function udim2ToCssWidth(u, pw) {
    return udim2AxisToCss(u.xScale, u.xOffset, pw);
}

function udim2ToCssHeight(u, ph) {
    return udim2AxisToCss(u.yScale, u.yOffset, ph);
}

function udim2AxisPixels(scale, offset, parentSize) {
    return (scale || 0) * parentSize + (offset || 0);
}

/**
 * Inner width/height of the immediate parent for UDim2 scale→px.
 * During a synchronous DOM build (e.g. after corner radius / full `renderFromLiveModel`), `clientWidth` on a Frame can still be 0.
 * Falling back to the full `previewSurface` size makes `scale * parent` use the wrong basis — children look ~2–3× too large.
 */
function getParentUdimBasisPx(parentEl) {
    const ps = previewSurface;
    const fbW = () => Math.max(1, ps?.clientWidth || 800);
    const fbH = () => Math.max(1, ps?.clientHeight || 600);
    if (!parentEl) return { w: fbW(), h: fbH() };
    if (parentEl === ps) return { w: fbW(), h: fbH() };
    if (parentEl._tridentComputedW > 0 && parentEl._tridentComputedH > 0) {
        return { w: parentEl._tridentComputedW, h: parentEl._tridentComputedH };
    }
    let w = parentEl.clientWidth;
    let h = parentEl.clientHeight;
    if (w < 1 || h < 1) {
        w = parentEl.offsetWidth || w;
        h = parentEl.offsetHeight || h;
    }
    if (w < 1) w = fbW();
    if (h < 1) h = fbH();
    return { w: Math.max(1, w), h: Math.max(1, h) };
}

function toAlphaColor(rgb, alpha) {
    const m = String(rgb).match(/^rgb\((\d+),\s*(\d+),\s*(\d+)\)$/);
    if (!m) return rgb;
    return `rgba(${m[1]}, ${m[2]}, ${m[3]}, ${alpha})`;
}

function computeRoots(model) {
    const childIds = new Set;
    for (const n of model.nodes.values()) {
        for (const c of n.children) childIds.add(c);
    }
    return [ ...model.nodes.keys() ].filter(id => !childIds.has(id));
}

function orderedRoots(model) {
    const roots = computeRoots(model);
    const idx = new Map;
    for (let i = 0; i < model.order.length; i++) {
        const id = model.order[i];
        if (!idx.has(id)) idx.set(id, i);
    }
    return [ ...roots ].sort((a, b) => (idx.get(a) ?? 1e9) - (idx.get(b) ?? 1e9));
}

function initEmptyDesign() {
    guiLayoutLockedIds.clear();
    const gui = "screenGui";
    const root = "rootFrame";
    liveModel.nodes.clear();
    liveModel.order = [];
    liveModel.nodes.set(gui, {
        id: gui,
        varName: gui,
        className: "ScreenGui",
        props: {
            Name: "TridentGui",
            IgnoreGuiInset: true,
            ResetOnSpawn: false,
            DisplayOrder: 1
        },
        children: [ root ]
    });
    liveModel.nodes.set(root, {
        id: root,
        varName: root,
        className: "Frame",
        props: {
            Name: "Frame",
            Size: {
                type: "udim2",
                xScale: .45,
                yScale: .45,
                xOffset: 0,
                yOffset: 0
            },
            Position: {
                type: "udim2",
                xScale: .275,
                yScale: .275,
                xOffset: 0,
                yOffset: 0
            },
            ZIndex: 1,
            BackgroundColor3: {
                type: "color3",
                r: 42,
                g: 46,
                b: 58
            },
            BorderSizePixel: 0
        },
        children: []
    });
    liveModel.order.push(gui, root);
    liveModel.roots = [ gui ];
}

function uniqueVarName(className, nodes, reservedExtra = null) {
    const base = (className || "Instance").replace(/[^a-zA-Z0-9]/g, "") || "Instance";
    const camel = base.charAt(0).toLowerCase() + base.slice(1);
    const used = new Set([ ...nodes.values() ].map(n => n.varName));
    if (reservedExtra) {
        for (const r of reservedExtra) {
            if (r) used.add(r);
        }
    }
    let name = camel;
    let i = 0;
    while (used.has(name)) {
        i += 1;
        name = `${camel}${i}`;
    }
    return name;
}

/** Returns a valid unused Lua identifier from user input, or null if unusable. */
function coerceLuaVarName(input, nodes, reservedExtra) {
    let t = String(input || "").trim().replace(/[^A-Za-z0-9_]/g, "");
    if (t && /^[0-9]/.test(t)) t = `_${t}`;
    if (!t || !/^[A-Za-z_][A-Za-z0-9_]*$/.test(t)) return null;
    const used = new Set([ ...nodes.values() ].map(n => n.varName));
    if (reservedExtra) {
        for (const r of reservedExtra) {
            if (r) used.add(r);
        }
    }
    let name = t;
    let i = 0;
    while (used.has(name)) {
        i += 1;
        name = `${t}${i}`;
    }
    return name;
}

function deepCloneNodeSnapshot(n) {
    return {
        id: n.id,
        varName: n.varName,
        className: n.className,
        props: JSON.parse(JSON.stringify(n.props)),
        children: [ ...(n.children || []) ]
    };
}

/** Build a serializable clipboard payload from top-level selected subtrees. */
function buildClipboardFromSelection() {
    const tops = getTopLevelSelectionIds();
    if (tops.length === 0) return null;
    const nodes = {};
    const roots = [];
    const seen = new Set;
    for (const rid of tops) {
        roots.push(rid);
        const stack = [ rid ];
        while (stack.length) {
            const id = stack.pop();
            if (seen.has(id)) continue;
            seen.add(id);
            const n = liveModel.nodes.get(id);
            if (!n) continue;
            nodes[id] = deepCloneNodeSnapshot(n);
            for (const c of n.children || []) stack.push(c);
        }
    }
    return {
        roots: roots,
        nodes: nodes
    };
}

let tridentClipboard = null;

/** Instantiate clipboard payload into liveModel. `opts.renameFirstRoot` must be an unused identifier if set. */
function pasteTridentPayload(clipboard, opts = {}) {
    if (!clipboard?.roots?.length || !clipboard.nodes || !liveModel?.nodes) return false;
    const { renameFirstRoot: renameFirstRoot = null } = opts;
    const reserved = new Set([ ...liveModel.nodes.keys() ]);
    const orderedOldIds = [];
    const visit = new Set;
    function bfsFrom(rootId) {
        const q = [ rootId ];
        while (q.length) {
            const id = q.shift();
            if (visit.has(id)) continue;
            visit.add(id);
            orderedOldIds.push(id);
            const n = clipboard.nodes[id];
            for (const c of n?.children || []) q.push(c);
        }
    }
    for (const r of clipboard.roots) bfsFrom(r);
    if (orderedOldIds.length === 0) return false;
    pushUndoState();
    const idMap = new Map;
    for (let i = 0; i < orderedOldIds.length; i++) {
        const oldId = orderedOldIds[i];
        const old = clipboard.nodes[oldId];
        if (!old) continue;
        const newId = i === 0 && renameFirstRoot ? renameFirstRoot : uniqueVarName(old.className, liveModel.nodes, reserved);
        reserved.add(newId);
        idMap.set(oldId, newId);
    }
    for (const oldId of orderedOldIds) {
        const old = clipboard.nodes[oldId];
        const newId = idMap.get(oldId);
        if (!old || !newId) continue;
        const newNode = {
            id: newId,
            varName: newId,
            className: old.className,
            props: JSON.parse(JSON.stringify(old.props)),
            children: (old.children || []).map(cid => idMap.get(cid)).filter(Boolean)
        };
        newNode.props.Name = newId;
        liveModel.nodes.set(newId, newNode);
        liveModel.order.push(newId);
    }
    const newRoots = clipboard.roots.map(r => idMap.get(r)).filter(Boolean);
    const pasteParent = findPasteParentForClipboard(liveModel);
    for (const nrId of newRoots) {
        const node = liveModel.nodes.get(nrId);
        if (!node) continue;
        if (node.className === "ScreenGui") {
            continue;
        }
        const parentId = coerceInsertParent(pasteParent, node.className, liveModel.nodes);
        if (parentId && liveModel.nodes.has(parentId)) {
            const par = liveModel.nodes.get(parentId);
            if (!par.children.includes(nrId)) par.children.push(nrId);
        }
    }
    liveModel.roots = orderedRoots(liveModel);
    const focusId = newRoots[0];
    if (focusId) {
        setSelectionSingle(focusId);
        expandedExplorerIds.add(parentVarFor(focusId, liveModel.nodes) || focusId);
    }
    guiLayoutLockedIds.clear();
    renderFromLiveModel();
    syncSourceFromModel();
    setStatus(newRoots.length > 1 ? `Pasted ${newRoots.length} roots` : "Pasted");
    return true;
}

function copyTridentSelection() {
    const payload = buildClipboardFromSelection();
    if (!payload) {
        setStatus("Nothing selected to copy");
        return;
    }
    tridentClipboard = payload;
    const n = payload.roots.length;
    setStatus(n > 1 ? `Copied ${n} subtrees` : "Copied");
}

function pasteTridentClipboard() {
    if (!tridentClipboard?.roots?.length) {
        setStatus("Nothing in clipboard — use ⌘C on the explorer / preview selection");
        return;
    }
    pasteTridentPayload(tridentClipboard, {});
}

function duplicateExplorerNodeInstant(nodeId) {
    if (!liveModel?.nodes?.has(nodeId)) return;
    const payload = buildClipboardFromSingleRoot(nodeId);
    if (!payload) return;
    pasteTridentPayload(payload, {});
}

function buildClipboardFromSingleRoot(rootId) {
    if (!liveModel.nodes.has(rootId)) return null;
    const nodes = {};
    const stack = [ rootId ];
    const seen = new Set;
    while (stack.length) {
        const id = stack.pop();
        if (seen.has(id)) continue;
        seen.add(id);
        const n = liveModel.nodes.get(id);
        if (!n) continue;
        nodes[id] = deepCloneNodeSnapshot(n);
        for (const c of n.children || []) stack.push(c);
    }
    return {
        roots: [ rootId ],
        nodes: nodes
    };
}

function findDefaultRootFrame(model) {
    const roots = computeRoots(model);
    for (const rid of roots) {
        const r = model.nodes.get(rid);
        if (r?.className === "ScreenGui") {
            for (const cid of r.children || []) {
                const c = model.nodes.get(cid);
                if (c?.className === "Frame") return cid;
            }
            return rid;
        }
    }
    for (const [, n] of model.nodes) {
        if (n.className === "Frame") return n.id;
    }
    return roots[0] || null;
}

function insertAllowed(parentClass, childClass) {
    if (!parentClass) return false;
    const decChild = DECORATOR_CLASSES.has(childClass) || LAYOUT_CLASSES.has(childClass);
    if (decChild) {
        return [ "Frame", "ScrollingFrame", "TextLabel", "TextButton", "TextBox", "ImageLabel", "ImageButton", "CanvasGroup", "ScreenGui" ].includes(parentClass);
    }
    if ([ "Frame", "ScrollingFrame", "CanvasGroup" ].includes(childClass)) {
        return [ "Frame", "ScrollingFrame", "ScreenGui", "CanvasGroup" ].includes(parentClass);
    }
    if ([ "TextLabel", "TextButton", "TextBox", "ImageLabel", "ImageButton" ].includes(childClass)) {
        return [ "Frame", "ScrollingFrame", "ScreenGui", "CanvasGroup" ].includes(parentClass);
    }
    return false;
}

/** Walk from drop target up until we find a valid Parent for childClass (e.g. drop on TextLabel → parent Frame). Skips the dragged node so you never “parent to self”. */
function findValidReparentParent(childId, childClass, dropTargetId, nodes) {
    let pid = dropTargetId;
    for (let hop = 0; hop < 64; hop++) {
        if (!pid || !nodes.has(pid)) return null;
        if (pid === childId) {
            pid = parentVarFor(pid, nodes);
            continue;
        }
        const p = nodes.get(pid);
        if (insertAllowed(p.className, childClass)) return pid;
        pid = parentVarFor(pid, nodes);
    }
    return null;
}

function isStrictDescendantOf(nodesMap, ancestorId, nodeId) {
    let id = nodeId;
    for (let hop = 0; hop < 4096; hop++) {
        const p = parentVarFor(id, nodesMap);
        if (!p) return false;
        if (p === ancestorId) return true;
        id = p;
    }
    return false;
}

function removeChildIdFromAllParents(nodesMap, childId) {
    for (const n of nodesMap.values()) {
        const idx = n.children.indexOf(childId);
        if (idx !== -1) n.children.splice(idx, 1);
    }
}

function reparentInstanceTo(childId, dropTargetId) {
    const child = liveModel.nodes.get(childId);
    if (!child || child.className === "ScreenGui") return false;
    const newParentId = findValidReparentParent(childId, child.className, dropTargetId, liveModel.nodes);
    if (!newParentId || newParentId === childId) return false;
    if (isStrictDescendantOf(liveModel.nodes, childId, newParentId)) return false;
    const oldP = parentVarFor(childId, liveModel.nodes);
    if (oldP === newParentId) return false;
    removeChildIdFromAllParents(liveModel.nodes, childId);
    liveModel.nodes.get(newParentId).children.push(childId);
    return true;
}

/** Reparent selection (or single dragged id) under drop target — e.g. onto ScreenGui, Frame, or a leaf (uses nearest valid ancestor). */
function reparentExplorerDrop(dropTargetId, primaryDragId) {
    if (!liveModel?.nodes?.has(dropTargetId) || !primaryDragId || !liveModel.nodes.has(primaryDragId)) return 0;
    const multi = selectedNodeIds.has(primaryDragId) && selectedNodeIds.size > 1;
    const ids = multi ? getTopLevelSelectionIds().filter(id => {
        const n = liveModel.nodes.get(id);
        return n && n.className !== "ScreenGui";
    }) : [ primaryDragId ].filter(id => {
        const n = liveModel.nodes.get(id);
        return n && n.className !== "ScreenGui";
    });
    if (ids.length === 0) return 0;
    pushUndoState();
    let ok = 0;
    for (const cid of ids) {
        if (reparentInstanceTo(cid, dropTargetId)) ok++;
    }
    if (ok === 0) {
        undoStack.pop();
        setStatus("Cannot reparent there");
        return 0;
    }
    expandedExplorerIds.add(dropTargetId);
    renderFromLiveModel();
    syncSourceFromModel();
    setStatus(ok > 1 ? `Reparented ${ok} instances` : "Reparented");
    return ok;
}

function coerceInsertParent(parentId, childClass, nodes) {
    let pid = parentId;
    for (let hop = 0; hop < 32; hop++) {
        if (!pid || !nodes.has(pid)) return findDefaultRootFrame({
            nodes: nodes,
            roots: computeRoots({
                nodes: nodes
            })
        });
        const p = nodes.get(pid);
        if (insertAllowed(p.className, childClass)) return pid;
        const up = parentVarFor(pid, nodes);
        pid = up;
    }
    return findDefaultRootFrame({
        nodes: nodes,
        roots: computeRoots({
            nodes: nodes
        })
    });
}

function findInsertParentId(model) {
    const primaryId = getPrimarySelectedId();
    if (!primaryId || !model.nodes.has(primaryId)) {
        return coerceInsertParent(findDefaultRootFrame(model), "Frame", model.nodes);
    }
    const sel = model.nodes.get(primaryId);
    let insertParent = sel.id;
    if (DECORATOR_CLASSES.has(sel.className) || LAYOUT_CLASSES.has(sel.className)) {
        insertParent = parentVarFor(sel.id, model.nodes) || findDefaultRootFrame(model);
    }
    return insertParent;
}

/** Parent to attach pasted/duplicated roots under (sibling of selection when possible). */
function findPasteParentForClipboard(model) {
    const primary = getPrimarySelectedId();
    if (!primary || !model.nodes.has(primary)) {
        return findInsertParentId(model);
    }
    const par = parentVarFor(primary, model.nodes);
    if (par) return par;
    const sel = model.nodes.get(primary);
    if (sel.className === "ScreenGui") return primary;
    return findInsertParentId(model);
}

function defaultPropsFor(className) {
    const base = {
        Name: className,
        Size: {
            type: "udim2",
            xScale: .28,
            yScale: .1,
            xOffset: 0,
            yOffset: 0
        },
        Position: {
            type: "udim2",
            xScale: .08,
            yScale: .12,
            xOffset: 0,
            yOffset: 0
        },
        ZIndex: 1,
        BackgroundColor3: {
            type: "color3",
            r: 42,
            g: 46,
            b: 58
        },
        BorderSizePixel: 0,
        BackgroundTransparency: 0,
        CornerRadius: {
            type: "udim",
            scale: 0,
            offset: 0
        },
        Draggable: false
    };
    const textAlignDefaults = {
        TextXAlignment: {
            type: "enumPath",
            path: "TextXAlignment.Center"
        },
        TextYAlignment: {
            type: "enumPath",
            path: "TextYAlignment.Center"
        }
    };
    if (className === "TextLabel" || className === "TextButton") {
        return {
            ...base,
            Text: className === "TextButton" ? "Button" : "Label",
            TextColor3: {
                type: "color3",
                r: 235,
                g: 238,
                b: 250
            },
            TextSize: 18,
            TextScaled: false,
            TextWrapped: false,
            ...textAlignDefaults
        };
    }
    if (className === "TextBox") {
        return {
            ...base,
            Text: "",
            TextColor3: {
                type: "color3",
                r: 235,
                g: 238,
                b: 250
            },
            TextSize: 14,
            TextScaled: false,
            TextWrapped: false,
            ...textAlignDefaults
        };
    }
    if (className === "ImageLabel" || className === "ImageButton") {
        return {
            ...base,
            BackgroundColor3: {
                type: "color3",
                r: 36,
                g: 40,
                b: 52
            },
            Image: ""
        };
    }
    if (className === "ScrollingFrame") {
        return {
            ...base,
            CanvasSize: {
                type: "udim2",
                xScale: 0,
                xOffset: 0,
                yScale: 0,
                yOffset: 320
            },
            ScrollBarThickness: 8
        };
    }
    if (className === "UICorner") {
        return {
            Name: "UICorner",
            CornerRadius: {
                type: "udim",
                scale: 0,
                offset: 8
            }
        };
    }
    if (className === "UIStroke") {
        return {
            Name: "UIStroke",
            Thickness: 1,
            Color: {
                type: "color3",
                r: 255,
                g: 255,
                b: 255
            },
            Transparency: 0
        };
    }
    if (className === "UIGradient") {
        return {
            Name: "UIGradient",
            Rotation: 0,
            Color: {
                type: "colorSequence",
                keypoints: [ {
                    time: 0,
                    color: [ 60, 80, 140 ]
                }, {
                    time: 1,
                    color: [ 35, 40, 55 ]
                } ]
            }
        };
    }
    if (className === "UIListLayout") {
        return {
            Name: "UIListLayout",
            FillDirection: {
                type: "enumPath",
                path: "FillDirection.Vertical"
            },
            HorizontalAlignment: {
                type: "enumPath",
                path: "HorizontalAlignment.Center"
            },
            VerticalAlignment: {
                type: "enumPath",
                path: "VerticalAlignment.Top"
            },
            Padding: {
                type: "udim",
                scale: 0,
                offset: 8
            }
        };
    }
    if (className === "UIPadding") {
        const u = {
            type: "udim",
            scale: 0,
            offset: 8
        };
        return {
            Name: "UIPadding",
            PaddingTop: u,
            PaddingBottom: u,
            PaddingLeft: u,
            PaddingRight: u
        };
    }
    if (className === "ScreenGui") {
        return {
            Name: "ScreenGui",
            IgnoreGuiInset: true,
            ResetOnSpawn: false,
            DisplayOrder: 1
        };
    }
    return {
        ...base
    };
}

function insertInstance(className, explicitParentId) {
    if (!liveModel?.nodes) return;
    if (liveModel.nodes.size === 0) initEmptyDesign();
    if (className === "ScreenGui") {
        pushUndoState();
        const varName = uniqueVarName("ScreenGui", liveModel.nodes);
        const newNode = {
            id: varName,
            varName: varName,
            className: "ScreenGui",
            props: defaultPropsFor("ScreenGui"),
            children: []
        };
        liveModel.nodes.set(varName, newNode);
        liveModel.order.push(varName);
        liveModel.roots = orderedRoots(liveModel);
        expandedExplorerIds.add(varName);
        setSelectionSingle(varName);
        renderFromLiveModel();
        syncSourceFromModel();
        setStatus(`Inserted ScreenGui · ${varName} (root)`);
        return;
    }
    let parentId = explicitParentId != null ? explicitParentId : findInsertParentId(liveModel);
    parentId = coerceInsertParent(parentId, className, liveModel.nodes);
    if (!parentId || !liveModel.nodes.has(parentId)) return;
    pushUndoState();
    const parent = liveModel.nodes.get(parentId);
    const varName = uniqueVarName(className, liveModel.nodes);
    const newNode = {
        id: varName,
        varName: varName,
        className: className,
        props: defaultPropsFor(className),
        children: []
    };
    liveModel.nodes.set(varName, newNode);
    liveModel.order.push(varName);
    parent.children.push(varName);
    liveModel.roots = orderedRoots(liveModel);
    expandedExplorerIds.add(parentId);
    expandedExplorerIds.add(varName);
    setSelectionSingle(varName);
    renderFromLiveModel();
    syncSourceFromModel();
    setStatus(`Inserted ${className} under ${parent.varName} as ${varName}`);
}

function usesLayoutPropsPanel(className) {
    if (className === "ScreenGui") return false;
    if (DECORATOR_CLASSES.has(className)) return false;
    if (LAYOUT_CLASSES.has(className)) return false;
    return true;
}

/** GuiObjects that can use exported UserInputService drag script. */
function supportsDraggableProp(className) {
    return [ "Frame", "ScrollingFrame", "CanvasGroup", "TextLabel", "TextButton", "TextBox", "ImageLabel", "ImageButton" ].includes(className);
}

function applyDraggableExportToSelection(wantTrue) {
    const targets = [ ...selectedNodeIds ].filter(id => {
        const n = liveModel.nodes.get(id);
        return n && usesLayoutPropsPanel(n.className) && supportsDraggableProp(n.className);
    });
    if (targets.length === 0) return;
    pushUndoState();
    for (const id of targets) {
        const p = liveModel.nodes.get(id).props;
        if (wantTrue) {
            p.TridentInputDrag = true;
            delete p.Draggable;
        } else {
            delete p.TridentInputDrag;
        }
    }
    renderFromLiveModel();
    syncSourceFromModel();
    refreshPropertiesPanel();
    setStatus(wantTrue ? `Input-drag script in Luau (${targets.length})` : `Input-drag removed from export (${targets.length})`);
}

function clearPreviewChrome() {
    if (!previewSurface) return;
    previewSurface.querySelectorAll(".trident-selected").forEach(x => x.classList.remove("trident-selected"));
    previewSurface.querySelectorAll(".trident-resize-handle").forEach(x => x.remove());
}

function tryHighlightSelectedInPreview() {
    highlightMultiSelected();
}

function highlightMultiSelected() {
    clearPreviewChrome();
    if (!liveModel?.nodes || selectedNodeIds.size === 0) return;
    for (const nodeId of selectedNodeIds) {
        const n = liveModel.nodes.get(nodeId);
        if (!n) continue;
        if (DECORATOR_CLASSES.has(n.className) || LAYOUT_CLASSES.has(n.className)) continue;
        const safe = String(nodeId).replace(/\\/g, "\\\\").replace(/"/g, '\\"');
        const el = previewSurface.querySelector(`[data-node-id="${safe}"]`);
        if (el && (!el.classList.contains("trident-viewport") || n.className === "ScreenGui")) {
            el.classList.add("trident-selected");
        }
    }
    const prim = getPrimarySelectedId();
    if (!prim || !liveModel.nodes.has(prim)) return;
    const pn = liveModel.nodes.get(prim);
    if (DECORATOR_CLASSES.has(pn.className) || LAYOUT_CLASSES.has(pn.className)) return;
    const safeP = String(prim).replace(/\\/g, "\\\\").replace(/"/g, '\\"');
    const pel = previewSurface.querySelector(`[data-node-id="${safeP}"]`);
    if (pel && (!pel.classList.contains("trident-viewport") || pn.className === "ScreenGui")) {
        repositionSelectionChrome(pel);
    }
}

function selectNodeById(id, opts) {
    if (!liveModel?.nodes?.has(id)) return;
    selectWithModifiers(id, opts);
    tryHighlightSelectedInPreview();
    refreshPropertiesPanel();
    refreshExplorer();
}

function refreshExplorer() {
    const tree = document.getElementById("explorerTree");
    if (!tree || !liveModel?.nodes) return;
    for (const id of [ ...expandedExplorerIds ]) {
        if (!liveModel.nodes.has(id)) expandedExplorerIds.delete(id);
    }
    if (expandedExplorerIds.size === 0 && liveModel.nodes.size > 0) {
        for (const id of liveModel.nodes.keys()) expandedExplorerIds.add(id);
    }
    tree.innerHTML = "";
    liveModel.roots = orderedRoots(liveModel);
    for (const rid of liveModel.roots) {
        appendExplorerNode(tree, rid, 0);
    }
}

function appendExplorerNode(container, nodeId, depth) {
    const n = liveModel.nodes.get(nodeId);
    if (!n) return;
    const row = document.createElement("div");
    row.className = "explorer-row";
    row.dataset.explorerId = nodeId;
    row.style.paddingLeft = `${2 + depth * 14}px`;
    if (selectedNodeIds.has(nodeId)) row.classList.add("explorer-row--selected");
    const kids = n.children || [];
    const hasKids = kids.length > 0;
    const toggle = document.createElement("span");
    toggle.className = hasKids ? "explorer-toggle" : "explorer-toggle explorer-toggle--leaf";
    toggle.textContent = hasKids ? expandedExplorerIds.has(nodeId) ? "▼" : "▶" : "";
    toggle.addEventListener("click", e => {
        e.stopPropagation();
        if (!hasKids) return;
        if (expandedExplorerIds.has(nodeId)) expandedExplorerIds.delete(nodeId); else expandedExplorerIds.add(nodeId);
        refreshExplorer();
    });
    const cls = document.createElement("span");
    cls.className = "explorer-class";
    cls.textContent = n.className;
    const nm = document.createElement("span");
    nm.className = "explorer-name";
    nm.textContent = n.varName;
    const cloneBtn = document.createElement("button");
    cloneBtn.type = "button";
    cloneBtn.className = "explorer-clone-btn";
    cloneBtn.title = "Duplicate (⌘C / ⌘V)";
    cloneBtn.setAttribute("aria-label", "Duplicate instance");
    cloneBtn.textContent = "⎘";
    cloneBtn.addEventListener("click", e => {
        e.stopPropagation();
        duplicateExplorerNodeInstant(nodeId);
    });
    const main = document.createElement("span");
    main.className = "explorer-row-main";
    main.appendChild(cls);
    main.appendChild(nm);
    row.appendChild(toggle);
    row.appendChild(main);
    row.appendChild(cloneBtn);
    row.draggable = true;
    row.addEventListener("dragstart", e => {
        e.dataTransfer.setData("application/x-trident-node-id", nodeId);
        e.dataTransfer.setData("text/plain", nodeId);
        e.dataTransfer.effectAllowed = "move";
    });
    row.addEventListener("click", e => {
        if (e.target.closest(".explorer-toggle") || e.target.closest(".explorer-clone-btn")) return;
        selectNodeById(nodeId, {
            additive: e.shiftKey,
            toggle: e.metaKey || e.ctrlKey
        });
    });
    row.addEventListener("dragover", e => {
        e.preventDefault();
        const types = Array.from(e.dataTransfer?.types || []);
        const fromChip = types.includes("application/x-trident-class");
        e.dataTransfer.dropEffect = fromChip ? "copy" : "move";
        row.classList.add("explorer-row--drop");
    });
    row.addEventListener("dragleave", () => row.classList.remove("explorer-row--drop"));
    row.addEventListener("drop", e => {
        e.preventDefault();
        row.classList.remove("explorer-row--drop");
        const clsName = e.dataTransfer.getData("application/x-trident-class");
        const moveId = e.dataTransfer.getData("application/x-trident-node-id");
        if (clsName) {
            insertInstance(clsName, nodeId);
            return;
        }
        if (moveId) {
            reparentExplorerDrop(nodeId, moveId);
        }
    });
    container.appendChild(row);
    if (!hasKids || !expandedExplorerIds.has(nodeId)) return;
    for (const cid of kids) {
        appendExplorerNode(container, cid, depth + 1);
    }
}

function deleteNodeById(id, skipUndo) {
    if (!id || !liveModel.nodes.has(id)) return;
    if (!skipUndo) pushUndoState();
    guiLayoutLockedIds.delete(id);
    function removeTree(nid) {
        const n = liveModel.nodes.get(nid);
        if (!n) return;
        for (const c of [ ...n.children ]) removeTree(c);
        for (const [, p] of liveModel.nodes) {
            p.children = p.children.filter(x => x !== nid);
        }
        liveModel.nodes.delete(nid);
        liveModel.order = liveModel.order.filter(x => x !== nid);
    }
    removeTree(id);
    if (liveModel.nodes.size === 0) {
        initEmptyDesign();
        setSelectionSingle(null);
        renderFromLiveModel();
        syncSourceFromModel();
        setStatus("Empty — started a new ScreenGui + Frame");
        return;
    }
    liveModel.roots = orderedRoots(liveModel);
    selectedNodeIds.delete(id);
    if (primarySelectedId === id) primarySelectedId = getPrimarySelectedId();
    renderFromLiveModel();
    syncSourceFromModel();
    setStatus("Deleted instance");
}

function deleteSelection() {
    const tops = getTopLevelSelectionIds();
    if (tops.length === 0) return;
    pushUndoState();
    for (const id of tops) {
        if (liveModel.nodes.has(id)) deleteNodeById(id, true);
    }
}

function setEditorSourceValue(text) {
    if (!input) return;
    input.value = text;
}

function syncSourceFromModel() {
    if (!input) return;
    setEditorSourceValue(exportToLuau(liveModel, getExportOpts()));
    schedulePersistEditorState();
}

function getEditorSnapshot() {
    const active = document.querySelector("#parentMountBar .parent-mount-btn.active");
    return {
        version: 1,
        source: input?.value ?? "",
        mount: active?.dataset?.mount || "playerGui",
        liveApply: propsLiveApply ? propsLiveApply.checked !== false : true
    };
}

function applyEditorSnapshot(snap) {
    if (!snap || typeof snap !== "object") return;
    if (typeof snap.source === "string") setEditorSourceValue(snap.source);
    if (snap.mount) {
        document.querySelectorAll("#parentMountBar .parent-mount-btn").forEach(btn => {
            btn.classList.toggle("active", btn.dataset.mount === snap.mount);
        });
    }
    if (typeof snap.liveApply === "boolean" && propsLiveApply) propsLiveApply.checked = snap.liveApply;
}

function schedulePersistEditorState() {
    clearTimeout(persistEditorTimer);
    persistEditorTimer = setTimeout(() => {
        persistEditorTimer = null;
        try {
            localStorage.setItem(TRIDENT_STORAGE_KEY, JSON.stringify(getEditorSnapshot()));
        } catch (err) {
            console.warn("Trident: could not persist editor state", err);
        }
    }, 250);
}

function downloadProjectJsonFile() {
    const name = (window.prompt("Project file name (without extension):", "my-trident-ui") || "trident-project").trim().replace(/[^\w\-]+/g, "_") || "trident-project";
    const snap = getEditorSnapshot();
    snap.savedAt = (new Date).toISOString();
    snap.label = name;
    const filename = `${name}.trident.json`;
    const blob = new Blob([ JSON.stringify(snap, null, 2) ], {
        type: "application/json;charset=utf-8"
    });
    const a = document.createElement("a");
    a.href = URL.createObjectURL(blob);
    a.download = filename;
    a.click();
    URL.revokeObjectURL(a.href);
    setStatus(`Saved project · ${filename}`);
}

function loadProjectFromJsonText(text) {
    const snap = JSON.parse(text);
    if (typeof snap.source !== "string") throw new Error("Invalid project: missing source string");
    errorBox.textContent = "";
    undoStack.length = 0;
    redoStack.length = 0;
    applyEditorSnapshot(snap);
    render();
    schedulePersistEditorState();
}

function renderFromLiveModel() {
    if (!liveModel?.nodes) return;
    endTextButtonInlineEdit(true);
    cancelTextButtonDragPending();
    liveModel.roots = orderedRoots(liveModel);
    errorBox.textContent = "";
    previewSurface.innerHTML = "";
    const roots = liveModel.roots;
    const nR = roots.length;
    for (let i = 0; i < nR; i++) {
        const rid = roots[i];
        const wrap = document.createElement("div");
        wrap.className = "trident-root-wrap";
        wrap.dataset.rootIndex = String(i);
        wrap.style.top = nR > 1 ? `${100 / nR * i}%` : "0";
        wrap.style.height = nR > 1 ? `${100 / nR}%` : "100%";
        if (nR > 1 && i < nR - 1) wrap.style.borderBottom = "1px solid rgba(255,255,255,0.1)";
        const surfW = previewSurface.clientWidth || 800;
        const surfH = previewSurface.clientHeight || 600;
        wrap._tridentComputedW = surfW;
        wrap._tridentComputedH = nR > 1 ? surfH / nR : surfH;
        const html = buildHtmlTree(rid, liveModel.nodes, wrap, true);
        if (html) wrap.appendChild(html);
        previewSurface.appendChild(wrap);
    }
    installEditor(previewSurface);
    sanitizeSelectionAfterModelChange();
    tryHighlightSelectedInPreview();
    ensureSnapLayer();
    if (!liveApplyingFromForm) refreshPropertiesPanel();
    refreshExplorer();
}

function color3ToRgbFields(c) {
    if (c && c.type === "color3") return {
        r: c.r,
        g: c.g,
        b: c.b
    };
    return {
        r: 255,
        g: 255,
        b: 255
    };
}

function buildInstancePath(nodeId, nodesMap) {
    const parts = [];
    let id = nodeId;
    while (id) {
        const node = nodesMap.get(id);
        if (!node) break;
        parts.unshift(node.varName);
        id = parentVarFor(id, nodesMap);
    }
    return parts.join(".");
}

function writePropFieldUnlessFocused(elementId, value) {
    const el = document.getElementById(elementId);
    if (!el || document.activeElement === el) return;
    el.value = value;
}

function refreshPropertiesPanel() {
    if (!propsForm || !propsEmpty) return;
    const primary = getPrimarySelectedId();
    const notice = document.getElementById("propsMixedNotice");
    const editorFields = document.getElementById("propsEditorFields");
    const propsApplyBtn = document.getElementById("propsApply");
    if (!primary || !liveModel.nodes.has(primary)) {
        propsEmpty.style.display = "";
        propsForm.style.display = "none";
        if (notice) notice.style.display = "none";
        if (editorFields) editorFields.style.display = "";
        if (propsApplyBtn) propsApplyBtn.disabled = false;
        return;
    }
    const selIds = [ ...selectedNodeIds ].filter(id => liveModel.nodes.has(id));
    const mixed = selIds.length > 1 && !selectionHasUniformClass();
    propsEmpty.style.display = "none";
    propsForm.style.display = "";
    if (mixed) {
        if (notice) notice.style.display = "";
        if (editorFields) editorFields.style.display = "none";
        if (propsApplyBtn) propsApplyBtn.disabled = true;
        propsClassReadout.textContent = `Mixed (${selIds.length})`;
        if (propsHierarchyReadout) {
            propsHierarchyReadout.textContent = [ ...new Set(selIds.map(id => liveModel.nodes.get(id).className)) ].join(", ");
        }
        return;
    }
    if (notice) notice.style.display = "none";
    if (editorFields) editorFields.style.display = "";
    if (propsApplyBtn) propsApplyBtn.disabled = false;
    suppressLayoutUnlockFromPropsRefresh = true;
    try {
    const n = liveModel.nodes.get(primary);
    const nSel = selIds.length;
    propsClassReadout.textContent = nSel > 1 ? `${n.className} (${nSel})` : n.className;
    if (propsHierarchyReadout) {
        propsHierarchyReadout.textContent = buildInstancePath(primary, liveModel.nodes);
    }
    const p = n.props;
    writePropFieldUnlessFocused("propsName", typeof p.Name === "string" ? p.Name : n.className);
    const sz = p.Size?.type === "udim2" ? p.Size : {
        xScale: .2,
        yScale: .1,
        xOffset: 0,
        yOffset: 0
    };
    const pos = p.Position?.type === "udim2" ? p.Position : {
        xScale: 0,
        yScale: 0,
        xOffset: 0,
        yOffset: 0
    };
    document.getElementById("propsSizeX").value = scaleToInputString(sz.xScale ?? 0);
    document.getElementById("propsSizeY").value = scaleToInputString(sz.yScale ?? 0);
    document.getElementById("propsPosX").value = scaleToInputString(pos.xScale ?? 0);
    document.getElementById("propsPosY").value = scaleToInputString(pos.yScale ?? 0);
    const ap = p.AnchorPoint?.type === "vector2" ? p.AnchorPoint : {
        x: 0,
        y: 0
    };
    document.getElementById("propsAx").value = scaleToInputString(ap.x ?? 0);
    document.getElementById("propsAy").value = scaleToInputString(ap.y ?? 0);
    document.getElementById("propsZIndex").value = String(typeof p.ZIndex === "number" && Number.isFinite(p.ZIndex) ? Math.round(p.ZIndex) : 1);
    const bg = color3ToRgbFields(p.BackgroundColor3);
    document.getElementById("propsBgR").value = String(bg.r);
    document.getElementById("propsBgG").value = String(bg.g);
    document.getElementById("propsBgB").value = String(bg.b);
    updateBgColorPickerUI();
    writePropFieldUnlessFocused("propsBgTrans", numInputString(typeof p.BackgroundTransparency === "number" ? p.BackgroundTransparency : 0, "0"));
    document.getElementById("propsBorder").value = typeof p.BorderSizePixel === "number" ? String(p.BorderSizePixel) : "0";
    const elemCornerInp = document.getElementById("propsElemCorner");
    const elemCornerLab = document.querySelector('label[for="propsElemCorner"]');
    if (elemCornerInp) {
        const canCorner = supportsAutoUICorner(n.className);
        elemCornerInp.disabled = !canCorner;
        if (elemCornerLab) elemCornerLab.style.opacity = canCorner ? "" : "0.45";
        if (canCorner) {
            const u = p.CornerRadius;
            const off = u && u.type === "udim" && Number.isFinite(u.offset) ? Math.min(64, Math.max(0, u.offset)) : 0;
            writePropFieldUnlessFocused("propsElemCorner", numInputString(off, "0"));
        }
    }
    writePropFieldUnlessFocused("propsText", typeof p.Text === "string" ? p.Text : "");
    const tx = color3ToRgbFields(p.TextColor3);
    document.getElementById("propsTxR").value = String(tx.r);
    document.getElementById("propsTxG").value = String(tx.g);
    document.getElementById("propsTxB").value = String(tx.b);
    document.getElementById("propsTextSize").value = typeof p.TextSize === "number" ? String(p.TextSize) : "18";
    document.getElementById("propsTextScaled").checked = p.TextScaled === true;
    document.getElementById("propsTextWrapped").checked = p.TextWrapped === true;
    const txEl = document.getElementById("propsTextXAlignment");
    const tyEl = document.getElementById("propsTextYAlignment");
    if (txEl) txEl.value = enumPathSuffix(p.TextXAlignment, "Center");
    if (tyEl) tyEl.value = enumPathSuffix(p.TextYAlignment, "Center");
    document.getElementById("propsImage").value = typeof p.Image === "string" ? p.Image : "";
    const textBlock = document.getElementById("propsTextBlock");
    if (textBlock) {
        textBlock.style.display = [ "TextLabel", "TextButton", "TextBox" ].includes(n.className) ? "contents" : "none";
    }
    const imageRow = document.getElementById("propsImageRow");
    if (imageRow) {
        imageRow.style.display = [ "ImageLabel", "ImageButton" ].includes(n.className) ? "contents" : "none";
    }
    const layoutBlock = document.getElementById("propsLayoutBlock");
    if (layoutBlock) {
        layoutBlock.style.display = usesLayoutPropsPanel(n.className) ? "contents" : "none";
    }
    const dragRow = document.getElementById("propsDraggableRow");
    const makeDragBtn = document.getElementById("propsMakeDraggableBtn");
    const clearDragBtn = document.getElementById("propsClearDraggableBtn");
    if (dragRow) {
        const showDrag = usesLayoutPropsPanel(n.className) && supportsDraggableProp(n.className);
        dragRow.style.display = showDrag ? "flex" : "none";
        if (showDrag && makeDragBtn && clearDragBtn) {
            const draggableIds = selIds.filter(id => {
                const nn = liveModel.nodes.get(id);
                return nn && usesLayoutPropsPanel(nn.className) && supportsDraggableProp(nn.className);
            });
            const allOn = draggableIds.length > 0 && draggableIds.every(id => liveModel.nodes.get(id).props.TridentInputDrag === true);
            makeDragBtn.disabled = draggableIds.length === 0;
            clearDragBtn.disabled = draggableIds.length === 0;
            makeDragBtn.setAttribute("aria-pressed", allOn ? "true" : "false");
        }
    }
    const sgFields = document.getElementById("propsScreenGuiFields");
    if (sgFields) sgFields.classList.toggle("is-visible", n.className === "ScreenGui");
    if (n.className === "ScreenGui") {
        const ig = document.getElementById("propsIgnoreGuiInset");
        const rs = document.getElementById("propsResetOnSpawn");
        const z = document.getElementById("propsSgZ");
        if (ig) ig.checked = p.IgnoreGuiInset !== false;
        if (rs) rs.checked = p.ResetOnSpawn === true;
        if (z) {
            const legacy = typeof p.ZIndex === "number" && Number.isFinite(p.ZIndex) ? Math.round(p.ZIndex) : null;
            const d = typeof p.DisplayOrder === "number" && Number.isFinite(p.DisplayOrder) ? Math.round(p.DisplayOrder) : legacy != null ? legacy : 1;
            z.value = String(Math.max(0, Math.min(2147483647, d)));
        }
    }
    const uic = document.getElementById("propsUICornerFields");
    const uis = document.getElementById("propsUIStrokeFields");
    const uig = document.getElementById("propsUIGradientFields");
    const uipad = document.getElementById("propsUIPaddingFields");
    if (uic) uic.classList.toggle("is-visible", n.className === "UICorner");
    if (uis) uis.classList.toggle("is-visible", n.className === "UIStroke");
    if (uig) uig.classList.toggle("is-visible", n.className === "UIGradient");
    if (uipad) uipad.classList.toggle("is-visible", n.className === "UIPadding");
    if (n.className === "UICorner") {
        const cr = p.CornerRadius?.type === "udim" && Number.isFinite(p.CornerRadius.offset) ? p.CornerRadius.offset : 8;
        writePropFieldUnlessFocused("propsCornerRadius", numInputString(Math.min(64, Math.max(0, cr)), "8"));
    }
    if (n.className === "UIStroke") {
        document.getElementById("propsStrokeThickness").value = String(typeof p.Thickness === "number" ? p.Thickness : 1);
        const sc = color3ToRgbFields(p.Color);
        document.getElementById("propsStrokeR").value = String(sc.r);
        document.getElementById("propsStrokeG").value = String(sc.g);
        document.getElementById("propsStrokeB").value = String(sc.b);
        writePropFieldUnlessFocused("propsStrokeTrans", numInputString(typeof p.Transparency === "number" ? p.Transparency : 0, "0"));
    }
    if (n.className === "UIGradient") {
        document.getElementById("propsGradRotation").value = String(typeof p.Rotation === "number" ? p.Rotation : 0);
    }
    if (n.className === "UIPadding") {
        const off = key => {
            const u = p[key];
            return u && u.type === "udim" && Number.isFinite(u.offset) ? Math.round(u.offset) : 0;
        };
        const pt = document.getElementById("propsPadTop");
        const pb = document.getElementById("propsPadBottom");
        const pl = document.getElementById("propsPadLeft");
        const pr = document.getElementById("propsPadRight");
        if (pt) pt.value = String(off("PaddingTop"));
        if (pb) pb.value = String(off("PaddingBottom"));
        if (pl) pl.value = String(off("PaddingLeft"));
        if (pr) pr.value = String(off("PaddingRight"));
    }
    for (const sid of selIds) {
        const sn = liveModel.nodes.get(sid);
        if (sn && usesLayoutPropsPanel(sn.className)) guiLayoutLockedIds.add(sid);
    }
    } finally {
        suppressLayoutUnlockFromPropsRefresh = false;
    }
}

function readNum(id, fallback = 0) {
    const v = parseFloat(document.getElementById(id)?.value);
    return Number.isFinite(v) ? v : fallback;
}

function scaleToInputString(v) {
    if (typeof v !== "number" || !Number.isFinite(v)) return "0";
    const t = Math.round(v * 1e9) / 1e9;
    return String(t);
}

function numInputString(v, fallback = "0") {
    if (typeof v !== "number" || !Number.isFinite(v)) return fallback;
    const t = Math.round(v * 10000) / 10000;
    return String(t);
}

/** Keep Position / Size / Anchor fields in the properties panel aligned with the model while dragging (one update per frame max). */
function schedulePropsLayoutInputsSyncDuringDrag(nodeId) {
    if (!nodeId || !liveModel?.nodes?.has(nodeId)) return;
    pendingPropsLayoutNodeId = nodeId;
    if (propsLayoutPanelSyncRaf) return;
    propsLayoutPanelSyncRaf = requestAnimationFrame(() => {
        propsLayoutPanelSyncRaf = 0;
        const id = pendingPropsLayoutNodeId;
        pendingPropsLayoutNodeId = null;
        if (!id || !liveModel.nodes.has(id)) return;
        if (!selectedNodeIds.has(id)) return;
        const n = liveModel.nodes.get(id);
        suppressLayoutUnlockFromPropsRefresh = true;
        try {
            const p = n.props;
            const sz = p.Size?.type === "udim2" ? p.Size : {
                xScale: .2,
                yScale: .1,
                xOffset: 0,
                yOffset: 0
            };
            const pos = p.Position?.type === "udim2" ? p.Position : {
                xScale: 0,
                yScale: 0,
                xOffset: 0,
                yOffset: 0
            };
            const ap = p.AnchorPoint?.type === "vector2" ? p.AnchorPoint : {
                x: 0,
                y: 0
            };
            const sx = document.getElementById("propsSizeX");
            const sy = document.getElementById("propsSizeY");
            const px = document.getElementById("propsPosX");
            const py = document.getElementById("propsPosY");
            const ax = document.getElementById("propsAx");
            const ay = document.getElementById("propsAy");
            if (sx) sx.value = scaleToInputString(sz.xScale ?? 0);
            if (sy) sy.value = scaleToInputString(sz.yScale ?? 0);
            if (px) px.value = scaleToInputString(pos.xScale ?? 0);
            if (py) py.value = scaleToInputString(pos.yScale ?? 0);
            if (ax) ax.value = scaleToInputString(ap.x ?? 0);
            if (ay) ay.value = scaleToInputString(ap.y ?? 0);
        } finally {
            suppressLayoutUnlockFromPropsRefresh = false;
        }
    });
}

function readInt(id, fallback = 0) {
    const v = parseInt(document.getElementById(id)?.value, 10);
    return Number.isFinite(v) ? v : fallback;
}

function applyPropsFromForm() {
    const targets = [ ...selectedNodeIds ].filter(id => liveModel.nodes.has(id));
    if (targets.length === 0) return;
    if (!selectionHasUniformClass()) return;
    const mergeLayoutFromForm = propsFormForceFullFormMerge || propsFormLayoutFieldsTouched;
    propsFormForceFullFormMerge = false;
    propsFormLayoutFieldsTouched = false;
    pushUndoState();
    liveApplyingFromForm = true;
    const primaryFormId = getPrimarySelectedId();
    try {
        for (const tid of targets) {
            const n = liveModel.nodes.get(tid);
            const p = n.props;
            if (n.className === "ScreenGui") {
                p.Name = document.getElementById("propsName").value || "ScreenGui";
                const ig = document.getElementById("propsIgnoreGuiInset");
                const rs = document.getElementById("propsResetOnSpawn");
                if (ig) p.IgnoreGuiInset = ig.checked;
                if (rs) p.ResetOnSpawn = rs.checked;
                p.DisplayOrder = Math.max(0, Math.min(2147483647, readInt("propsSgZ", 1)));
                migrateScreenGuiNodeProps(p);
                continue;
            }
            if (n.className === "UICorner") {
                p.Name = document.getElementById("propsName").value || "UICorner";
                const px = Math.min(64, Math.max(0, readNum("propsCornerRadius", 8)));
                p.CornerRadius = {
                    type: "udim",
                    scale: 0,
                    offset: px
                };
                continue;
            }
            if (n.className === "UIStroke") {
                p.Name = document.getElementById("propsName").value || "UIStroke";
                p.Thickness = Math.min(100, Math.max(0, readInt("propsStrokeThickness", 1)));
                p.Color = {
                    type: "color3",
                    r: Math.min(255, Math.max(0, readInt("propsStrokeR", 255))),
                    g: Math.min(255, Math.max(0, readInt("propsStrokeG", 255))),
                    b: Math.min(255, Math.max(0, readInt("propsStrokeB", 255)))
                };
                p.Transparency = Math.min(1, Math.max(0, readNum("propsStrokeTrans", 0)));
                continue;
            }
            if (n.className === "UIGradient") {
                p.Name = document.getElementById("propsName").value || "UIGradient";
                p.Rotation = Math.min(360, Math.max(-360, readInt("propsGradRotation", 0)));
                if (p.Color?.type !== "colorSequence" || !p.Color.keypoints?.length) {
                    p.Color = {
                        type: "colorSequence",
                        keypoints: [ {
                            time: 0,
                            color: [ 60, 80, 140 ]
                        }, {
                            time: 1,
                            color: [ 35, 40, 55 ]
                        } ]
                    };
                }
                continue;
            }
            if (n.className === "UIPadding") {
                p.Name = document.getElementById("propsName").value || "UIPadding";
                const side = id => ({
                    type: "udim",
                    scale: 0,
                    offset: Math.min(200, Math.max(0, readInt(id, 0)))
                });
                p.PaddingTop = side("propsPadTop");
                p.PaddingBottom = side("propsPadBottom");
                p.PaddingLeft = side("propsPadLeft");
                p.PaddingRight = side("propsPadRight");
                continue;
            }
            if (LAYOUT_CLASSES.has(n.className)) {
                p.Name = document.getElementById("propsName").value || n.className;
                continue;
            }
            p.Name = document.getElementById("propsName").value || n.className;
            const layoutLockedToPreview = guiLayoutLockedIds.has(tid);
            /** One props panel drives all targets; only the primary selection's layout fields match that row. Applying shared layout to every target would stomp non-primary sizes/positions (felt like random jumps). */
            const layoutFromSharedForm = targets.length === 1 || tid === primaryFormId;
            if (!layoutLockedToPreview && layoutFromSharedForm && mergeLayoutFromForm) {
                p.Size = {
                    type: "udim2",
                    xScale: readNum("propsSizeX", .2),
                    yScale: readNum("propsSizeY", .1),
                    xOffset: 0,
                    yOffset: 0
                };
                p.Position = {
                    type: "udim2",
                    xScale: readNum("propsPosX", 0),
                    yScale: readNum("propsPosY", 0),
                    xOffset: 0,
                    yOffset: 0
                };
                p.AnchorPoint = {
                    type: "vector2",
                    x: Math.min(1, Math.max(0, readNum("propsAx", 0))),
                    y: Math.min(1, Math.max(0, readNum("propsAy", 0)))
                };
            }
            p.ZIndex = Math.max(-32768, Math.min(32767, readInt("propsZIndex", 1)));
            p.BackgroundColor3 = {
                type: "color3",
                r: Math.min(255, Math.max(0, readInt("propsBgR", 40))),
                g: Math.min(255, Math.max(0, readInt("propsBgG", 44))),
                b: Math.min(255, Math.max(0, readInt("propsBgB", 58)))
            };
            p.BackgroundTransparency = Math.min(1, Math.max(0, readNum("propsBgTrans", 0)));
            p.BorderSizePixel = Math.min(100, Math.max(0, readInt("propsBorder", 0)));
            if (supportsAutoUICorner(n.className)) {
                const px = Math.min(64, Math.max(0, readNum("propsElemCorner", 0)));
                p.CornerRadius = {
                    type: "udim",
                    scale: 0,
                    offset: px
                };
            }
            if ([ "TextLabel", "TextButton", "TextBox" ].includes(n.className)) {
                p.Text = document.getElementById("propsText").value;
                p.TextColor3 = {
                    type: "color3",
                    r: Math.min(255, Math.max(0, readInt("propsTxR", 240))),
                    g: Math.min(255, Math.max(0, readInt("propsTxG", 240))),
                    b: Math.min(255, Math.max(0, readInt("propsTxB", 245)))
                };
                p.TextSize = Math.min(100, Math.max(6, readInt("propsTextSize", 18)));
                p.TextScaled = document.getElementById("propsTextScaled").checked;
                p.TextWrapped = document.getElementById("propsTextWrapped").checked;
                const tx = document.getElementById("propsTextXAlignment")?.value || "Center";
                const ty = document.getElementById("propsTextYAlignment")?.value || "Center";
                p.TextXAlignment = {
                    type: "enumPath",
                    path: `TextXAlignment.${tx}`
                };
                p.TextYAlignment = {
                    type: "enumPath",
                    path: `TextYAlignment.${ty}`
                };
            }
            if (n.className === "ImageLabel" || n.className === "ImageButton") {
                p.Image = document.getElementById("propsImage").value.trim();
            }
        }
        renderFromLiveModel();
        syncSourceFromModel();
        const one = liveModel.nodes.get(targets[0]);
        setStatus(targets.length > 1 ? `Updated ${targets.length} instances` : `Updated ${one.varName}`);
    } finally {
        refreshPropertiesPanel();
        liveApplyingFromForm = false;
    }
}

function rgbToHsv(r, g, b) {
    r /= 255;
    g /= 255;
    b /= 255;
    const max = Math.max(r, g, b);
    const min = Math.min(r, g, b);
    const d = max - min;
    let h = 0;
    if (d > 1e-10) {
        if (max === r) h = ((g - b) / d + (g < b ? 6 : 0)) / 6;
        else if (max === g) h = ((b - r) / d + 2) / 6;
        else h = ((r - g) / d + 4) / 6;
    }
    const s = max <= 1e-10 ? 0 : d / max;
    const v = max;
    return {
        h: h * 360,
        s: s,
        v: v
    };
}

function hsvToRgb(h, s, v) {
    const hh = (h % 360 + 360) % 360;
    const c = v * s;
    const x = c * (1 - Math.abs(hh / 60 % 2 - 1));
    const m = v - c;
    let r1 = 0;
    let g1 = 0;
    let b1 = 0;
    if (hh < 60) {
        r1 = c;
        g1 = x;
        b1 = 0;
    } else if (hh < 120) {
        r1 = x;
        g1 = c;
        b1 = 0;
    } else if (hh < 180) {
        r1 = 0;
        g1 = c;
        b1 = x;
    } else if (hh < 240) {
        r1 = 0;
        g1 = x;
        b1 = c;
    } else if (hh < 300) {
        r1 = x;
        g1 = 0;
        b1 = c;
    } else {
        r1 = c;
        g1 = 0;
        b1 = x;
    }
    return {
        r: Math.min(255, Math.max(0, Math.round((r1 + m) * 255))),
        g: Math.min(255, Math.max(0, Math.round((g1 + m) * 255))),
        b: Math.min(255, Math.max(0, Math.round((b1 + m) * 255)))
    };
}

function updateBgColorPickerUI() {
    const picker = document.getElementById("propsBgColorPicker");
    const dot = document.getElementById("propsBgSvDot");
    const thumb = document.getElementById("propsBgHueThumb");
    const hueStrip = document.getElementById("propsBgHueStrip");
    if (!picker || !dot || !thumb) return;
    const r = readInt("propsBgR", 40);
    const g = readInt("propsBgG", 44);
    const b = readInt("propsBgB", 58);
    const { h: h, s: s, v: v } = rgbToHsv(r, g, b);
    picker.style.setProperty("--cp-hue", String(Math.round(h)));
    dot.style.left = `${s * 100}%`;
    dot.style.top = `${(1 - v) * 100}%`;
    thumb.style.left = `${h / 360 * 100}%`;
    if (hueStrip) hueStrip.setAttribute("aria-valuenow", String(Math.round(h)));
}

function setPropsBgRgbFromPicker(rgb) {
    const rEl = document.getElementById("propsBgR");
    const gEl = document.getElementById("propsBgG");
    const bEl = document.getElementById("propsBgB");
    if (!rEl || !gEl || !bEl) return;
    rEl.value = String(rgb.r);
    gEl.value = String(rgb.g);
    bEl.value = String(rgb.b);
    updateBgColorPickerUI();
    applyPropsFromForm();
}

function installBgColorPicker() {
    const hueStrip = document.getElementById("propsBgHueStrip");
    const svPad = document.getElementById("propsBgSvPad");
    if (!hueStrip || !svPad || hueStrip.dataset.tridentPickerInstalled) return;
    hueStrip.dataset.tridentPickerInstalled = "1";
    let dragKind = null;
    let capId = null;
    function hueFromClientX(clientX) {
        const rect = hueStrip.getBoundingClientRect();
        const x = Math.max(0, Math.min(1, (clientX - rect.left) / Math.max(1, rect.width)));
        return x * 360;
    }
    function svFromClient(clientX, clientY) {
        const rect = svPad.getBoundingClientRect();
        const x = Math.max(0, Math.min(1, (clientX - rect.left) / Math.max(1, rect.width)));
        const y = Math.max(0, Math.min(1, (clientY - rect.top) / Math.max(1, rect.height)));
        return {
            s: x,
            v: 1 - y
        };
    }
    function applyHue(e) {
        const h = hueFromClientX(e.clientX);
        const r0 = readInt("propsBgR", 0);
        const g0 = readInt("propsBgG", 0);
        const b0 = readInt("propsBgB", 0);
        const { s: s, v: v } = rgbToHsv(r0, g0, b0);
        setPropsBgRgbFromPicker(hsvToRgb(h, s, v));
    }
    function applySv(e) {
        const { s: s, v: v } = svFromClient(e.clientX, e.clientY);
        const r0 = readInt("propsBgR", 0);
        const g0 = readInt("propsBgG", 0);
        const b0 = readInt("propsBgB", 0);
        const { h: h } = rgbToHsv(r0, g0, b0);
        setPropsBgRgbFromPicker(hsvToRgb(h, s, v));
    }
    function onPointerMove(e) {
        if (capId != null && e.pointerId !== capId) return;
        if (dragKind === "hue") applyHue(e);
        else if (dragKind === "sv") applySv(e);
    }
    function onPointerUp(e) {
        if (capId != null && e.pointerId !== capId) return;
        try {
            hueStrip.releasePointerCapture(e.pointerId);
        } catch (_) {}
        try {
            svPad.releasePointerCapture(e.pointerId);
        } catch (_) {}
        dragKind = null;
        capId = null;
        window.removeEventListener("pointermove", onPointerMove);
        window.removeEventListener("pointerup", onPointerUp);
        window.removeEventListener("pointercancel", onPointerUp);
    }
    hueStrip.addEventListener("pointerdown", e => {
        if (e.button !== 0) return;
        e.preventDefault();
        dragKind = "hue";
        capId = e.pointerId;
        try {
            hueStrip.setPointerCapture(e.pointerId);
        } catch (_) {}
        window.addEventListener("pointermove", onPointerMove);
        window.addEventListener("pointerup", onPointerUp);
        window.addEventListener("pointercancel", onPointerUp);
        applyHue(e);
    });
    svPad.addEventListener("pointerdown", e => {
        if (e.button !== 0) return;
        e.preventDefault();
        dragKind = "sv";
        capId = e.pointerId;
        try {
            svPad.setPointerCapture(e.pointerId);
        } catch (_) {}
        window.addEventListener("pointermove", onPointerMove);
        window.addEventListener("pointerup", onPointerUp);
        window.addEventListener("pointercancel", onPointerUp);
        applySv(e);
    });
}

function installEditor(surface) {
    if (surface.dataset.tridentEditorInstalled) return;
    surface.dataset.tridentEditorInstalled = "1";
    surface.addEventListener("pointerdown", e => {
        if (e.button !== 0) return;
        if (e.target === surface) {
            cancelTextButtonDragPending();
            clearSelection(surface);
            refreshPropertiesPanel();
            refreshExplorer();
            return;
        }
        if (e.target.closest(".trident-resize-handle")) return;
        const el = e.target.closest(".roblox-ui");
        if (!el || !surface.contains(el)) return;
        cancelTextButtonDragPending();
        if (el.classList.contains("trident-viewport")) {
            if (el.dataset.className === "ScreenGui") {
                selectWithModifiers(el.dataset.nodeId, {
                    additive: e.shiftKey,
                    toggle: e.metaKey || e.ctrlKey
                });
                highlightMultiSelected();
                refreshPropertiesPanel();
                refreshExplorer();
                return;
            }
            clearSelection(surface);
            refreshPropertiesPanel();
            refreshExplorer();
            return;
        }
        if (el.dataset.className === "TextButton" && el.classList.contains("trident-tb-inline-edit")) {
            return;
        }
        selectWithModifiers(el.dataset.nodeId, {
            additive: e.shiftKey,
            toggle: e.metaKey || e.ctrlKey
        });
        highlightMultiSelected();
        refreshPropertiesPanel();
        refreshExplorer();
        const er = el.getBoundingClientRect();
        const grabX = e.clientX - er.left;
        const grabY = e.clientY - er.top;
        const needsDragThreshold = e.shiftKey || e.metaKey || e.ctrlKey || el.dataset.className === "TextButton";
        if (needsDragThreshold) {
            const startX = e.clientX;
            const startY = e.clientY;
            const pointerId = e.pointerId;
            const onMove = ev => {
                if (!textButtonDragPending || ev.pointerId !== pointerId) return;
                if (Math.hypot(ev.clientX - startX, ev.clientY - startY) < 6) return;
                const p = textButtonDragPending;
                cancelTextButtonDragPending();
                startMoveDrag(ev, p.el, p.el, p.grabX, p.grabY);
            };
            const onUp = ev => {
                if (ev.pointerId !== pointerId) return;
                cancelTextButtonDragPending();
            };
            textButtonDragPending = {
                el: el,
                grabX: grabX,
                grabY: grabY,
                onMove: onMove,
                onUp: onUp
            };
            window.addEventListener("pointermove", onMove);
            window.addEventListener("pointerup", onUp);
            window.addEventListener("pointercancel", onUp);
            return;
        }
        startMoveDrag(e, el, el, grabX, grabY);
    }, true);
    surface.addEventListener("dblclick", e => {
        const el = e.target.closest(".roblox-ui");
        if (!el || !surface.contains(el) || el.classList.contains("trident-viewport")) return;
        if (el.dataset.className !== "TextButton") return;
        e.preventDefault();
        e.stopPropagation();
        beginTextButtonInlineEdit(el);
    }, true);
}

function clearSelection(surface) {
    endTextButtonInlineEdit(true);
    setSelectionSingle(null);
    surface.querySelectorAll(".trident-selected").forEach(x => x.classList.remove("trident-selected"));
    surface.querySelectorAll(".trident-resize-handle").forEach(x => x.remove());
    refreshExplorer();
}

function cancelTextButtonDragPending() {
    if (!textButtonDragPending) return;
    const t = textButtonDragPending;
    window.removeEventListener("pointermove", t.onMove);
    window.removeEventListener("pointerup", t.onUp);
    window.removeEventListener("pointercancel", t.onUp);
    textButtonDragPending = null;
}

function endTextButtonInlineEdit(commit) {
    if (!textButtonEditEl) return;
    const el = textButtonEditEl;
    const nodeId = el.dataset.nodeId;
    const node = nodeId && liveModel?.nodes?.get(nodeId);
    if (textButtonEditKeydownHandler) {
        el.removeEventListener("keydown", textButtonEditKeydownHandler);
        textButtonEditKeydownHandler = null;
    }
    if (el._tridentTbOnBlur) {
        el.removeEventListener("blur", el._tridentTbOnBlur);
        delete el._tridentTbOnBlur;
    }
    el.contentEditable = "false";
    el.classList.remove("trident-tb-inline-edit");
    textButtonEditEl = null;
    if (commit && node) {
        const raw = (el.textContent ?? "").replace(/\u00a0/g, " ");
        node.props.Text = raw.length ? raw : " ";
        pushUndoState();
        syncSourceFromModel();
        refreshPropertiesPanel();
    } else if (!commit && node && typeof node.props.Text === "string") {
        el.textContent = node.props.Text;
    }
}

function beginTextButtonInlineEdit(el) {
    if (!el || el.dataset.className !== "TextButton") return;
    cancelTextButtonDragPending();
    if (textButtonEditEl && textButtonEditEl !== el) endTextButtonInlineEdit(true);
    if (textButtonEditEl === el) {
        el.focus();
        return;
    }
    setSelectionSingle(el.dataset.nodeId);
    highlightMultiSelected();
    refreshPropertiesPanel();
    refreshExplorer();
    textButtonEditEl = el;
    el.classList.add("trident-tb-inline-edit");
    el.contentEditable = "true";
    el.setAttribute("spellcheck", "false");
    el._tridentTbOnBlur = () => {
        if (textButtonEditEl === el) endTextButtonInlineEdit(true);
    };
    el.addEventListener("blur", el._tridentTbOnBlur);
    textButtonEditKeydownHandler = e => {
        if (e.key === "Escape") {
            e.preventDefault();
            e.stopPropagation();
            endTextButtonInlineEdit(false);
        }
    };
    el.addEventListener("keydown", textButtonEditKeydownHandler);
    requestAnimationFrame(() => {
        if (!textButtonEditEl || textButtonEditEl !== el) return;
        el.focus();
        const range = document.createRange();
        range.selectNodeContents(el);
        const sel = window.getSelection();
        sel.removeAllRanges();
        sel.addRange(range);
    });
}

function startMoveDrag(e, el, captureTarget, grabOffsetX, grabOffsetY) {
    const draggedId = el.dataset.nodeId;
    if (draggedId) guiLayoutLockedIds.delete(draggedId);
    clearSnapGuides();
    pushUndoState();
    const parent = el.offsetParent || previewSurface;
    const ct = captureTarget && document.contains(captureTarget) ? captureTarget : el;
    const companions = [];
    if (selectedNodeIds.size > 1 && selectedNodeIds.has(draggedId)) {
        for (const sid of selectedNodeIds) {
            if (sid === draggedId) continue;
            const safe = String(sid).replace(/\\/g, "\\\\").replace(/"/g, '\\"');
            const cel = previewSurface.querySelector(`[data-node-id="${safe}"]`);
            if (!cel || cel.classList.contains("trident-viewport")) continue;
            const cp = cel.offsetParent || previewSurface;
            if (cp !== parent) continue;
            guiLayoutLockedIds.delete(sid);
            companions.push({
                el: cel,
                baseLeft: cel.offsetLeft,
                baseTop: cel.offsetTop,
                w: cel.offsetWidth,
                h: cel.offsetHeight
            });
        }
    }
    const pb0 = getParentUdimBasisPx(parent);
    dragState = {
        kind: "move",
        el: el,
        captureTarget: ct,
        parent: parent,
        prW: pb0.w,
        prH: pb0.h,
        grabOffsetX: grabOffsetX,
        grabOffsetY: grabOffsetY,
        pointerId: e.pointerId,
        _raf: 0,
        _pending: null,
        startLeftPrimary: el.offsetLeft,
        startTopPrimary: el.offsetTop,
        companions: companions
    };
    try {
        ct.setPointerCapture(e.pointerId);
    } catch (_) {}
    window.addEventListener("pointermove", onPointerMove);
    window.addEventListener("pointerup", onPointerUp);
    window.addEventListener("pointercancel", onPointerUp);
}

function repositionSelectionChrome(el) {
    previewSurface.querySelectorAll(".trident-resize-handle").forEach(x => x.remove());
    if (el.dataset.className === "ScreenGui") return;
    addResizeHandles(el);
}

/** Move corner handles to match `el` without removing nodes (keeps active pointer capture during resize). */
function positionResizeHandlesAround(el) {
    if (!previewSurface || !el) return;
    if (el.dataset.className === "ScreenGui") return;
    const box = elementBoxInSurface(el);
    const left = box.left;
    const top = box.top;
    const w = box.w;
    const hgt = box.h;
    const hs = 8;
    const half = hs / 2;
    const corners = {
        nw: [ left - half, top - half ],
        ne: [ left + w - half, top - half ],
        sw: [ left - half, top + hgt - half ],
        se: [ left + w - half, top + hgt - half ]
    };
    previewSurface.querySelectorAll(".trident-resize-handle[data-corner]").forEach(h => {
        const pos = corners[h.dataset.corner];
        if (!pos) return;
        h.style.left = `${Math.round(pos[0])}px`;
        h.style.top = `${Math.round(pos[1])}px`;
    });
}

function addResizeHandles(el) {
    const box = elementBoxInSurface(el);
    const left = box.left;
    const top = box.top;
    const w = box.w;
    const hgt = box.h;
    const hs = 8;
    const half = hs / 2;
    const corners = [ "nw", "ne", "sw", "se" ];
    corners.forEach(c => {
        const h = document.createElement("div");
        h.className = "trident-resize-handle";
        h.dataset.tridentChrome = "1";
        h.dataset.corner = c;
        Object.assign(h.style, {
            position: "absolute",
            width: `${hs}px`,
            height: `${hs}px`,
            background: "var(--border-focus)",
            borderRadius: "2px",
            zIndex: zIndexForSelectionChrome(),
            pointerEvents: "auto",
            touchAction: "none",
            boxShadow: "0 0 0 1px rgba(0,0,0,0.45)"
        });
        if (c === "nw") {
            h.style.left = `${Math.round(left - half)}px`;
            h.style.top = `${Math.round(top - half)}px`;
        }
        if (c === "ne") {
            h.style.left = `${Math.round(left + w - half)}px`;
            h.style.top = `${Math.round(top - half)}px`;
        }
        if (c === "sw") {
            h.style.left = `${Math.round(left - half)}px`;
            h.style.top = `${Math.round(top + hgt - half)}px`;
        }
        if (c === "se") {
            h.style.left = `${Math.round(left + w - half)}px`;
            h.style.top = `${Math.round(top + hgt - half)}px`;
        }
        previewSurface.appendChild(h);
        h.addEventListener("pointerdown", ev => {
            ev.preventDefault();
            ev.stopPropagation();
            const rid = el.dataset.nodeId;
            if (rid) guiLayoutLockedIds.delete(rid);
            setSelectionSingle(el.dataset.nodeId);
            highlightMultiSelected();
            pushUndoState();
            const p = el.offsetParent || previewSurface;
            const pb1 = getParentUdimBasisPx(p);
            const handleEl = previewSurface.querySelector(`.trident-resize-handle[data-corner="${c}"]`);
            dragState = {
                kind: "resize",
                corner: c,
                el: el,
                captureTarget: handleEl || h,
                parent: p,
                prW: pb1.w,
                prH: pb1.h,
                startPointerX: ev.clientX,
                startPointerY: ev.clientY,
                startLeft: el.offsetLeft,
                startTop: el.offsetTop,
                w: el.offsetWidth,
                h: el.offsetHeight,
                pointerId: ev.pointerId,
                _raf: 0,
                _pending: null
            };
            try {
                (handleEl || h).setPointerCapture(ev.pointerId);
            } catch (_) {}
            window.addEventListener("pointermove", onPointerMove);
            window.addEventListener("pointerup", onPointerUp);
            window.addEventListener("pointercancel", onPointerUp);
        });
    });
}

function flushDragFrame() {
    const st = dragState;
    if (!st) return;
    const ev = st._pending;
    st._pending = null;
    if (ev) applyDragPointerMove(ev);
    st._raf = 0;
    if (st === dragState && st._pending) {
        st._raf = requestAnimationFrame(flushDragFrame);
    }
}

function onPointerMove(e) {
    if (!dragState) return;
    if (e.pointerId !== dragState.pointerId) return;
    dragState._pending = e;
    if (dragState._raf) return;
    dragState._raf = requestAnimationFrame(flushDragFrame);
}

function applyDragPointerMove(e) {
    if (!dragState) return;
    if (e.pointerId !== dragState.pointerId) return;
    const {kind: kind, el: el, parent: parent, startPointerX: startPointerX, startPointerY: startPointerY, startLeft: startLeft, startTop: startTop, w: w, h: h, corner: corner, grabOffsetX: grabOffsetX, grabOffsetY: grabOffsetY, startLeftPrimary: startLeftPrimary, startTopPrimary: startTopPrimary, companions: companions} = dragState;
    const dx = e.clientX - startPointerX;
    const dy = e.clientY - startPointerY;
    if (kind === "move") {
        const prRect = parent.getBoundingClientRect();
        let nl = e.clientX - prRect.left - grabOffsetX;
        let nt = e.clientY - prRect.top - grabOffsetY;
        const ew = el.offsetWidth;
        const eh = el.offsetHeight;
        const snap = snapMoveWithGuides(el, nl, nt, ew, eh);
        renderSnapGuides(snap.vxSurf, snap.vySurf);
        el.style.left = `${snap.nl}px`;
        el.style.top = `${snap.nt}px`;
        syncNodeFromPixels(el);
        const dlx = snap.nl - startLeftPrimary;
        const dty = snap.nt - startTopPrimary;
        if (companions && companions.length) {
            for (const c of companions) {
                const nl2 = c.baseLeft + dlx;
                const nt2 = c.baseTop + dty;
                c.el.style.left = `${nl2}px`;
                c.el.style.top = `${nt2}px`;
                syncNodeFromPixels(c.el);
            }
        }
        schedulePropsLayoutInputsSyncDuringDrag(el.dataset.nodeId);
        positionResizeHandlesAround(el);
    } else if (kind === "resize") {
        clearSnapGuides();
        let nl = startLeft;
        let nt = startTop;
        let nw = w;
        let nh = h;
        if (corner === "se") {
            nw = Math.max(20, w + dx);
            nh = Math.max(20, h + dy);
        } else if (corner === "sw") {
            nl = Math.min(startLeft + dx, startLeft + w - 20);
            nw = Math.max(20, w - (nl - startLeft));
            nh = Math.max(20, h + dy);
        } else if (corner === "ne") {
            nw = Math.max(20, w + dx);
            nt = Math.min(startTop + dy, startTop + h - 20);
            nh = Math.max(20, h - (nt - startTop));
        } else if (corner === "nw") {
            nl = Math.min(startLeft + dx, startLeft + w - 20);
            nt = Math.min(startTop + dy, startTop + h - 20);
            nw = Math.max(20, w - (nl - startLeft));
            nh = Math.max(20, h - (nt - startTop));
        }
        el.style.left = `${nl}px`;
        el.style.top = `${nt}px`;
        el.style.width = `${nw}px`;
        el.style.height = `${nh}px`;
        syncNodeFromPixels(el);
        schedulePropsLayoutInputsSyncDuringDrag(el.dataset.nodeId);
        positionResizeHandlesAround(el);
    }
}

function onPointerUp(e) {
    const st = dragState;
    if (!st) return;
    if (e && typeof e.pointerId === "number" && e.pointerId !== st.pointerId) return;
    if (st._raf) {
        cancelAnimationFrame(st._raf);
        st._raf = 0;
        if (st._pending) applyDragPointerMove(st._pending);
        st._pending = null;
    }
    if (st.kind === "move" && st.el) {
        syncNodeFromPixels(st.el);
        for (const c of st.companions || []) {
            if (c?.el) syncNodeFromPixels(c.el);
        }
    } else if (st.kind === "resize" && st.el) {
        syncNodeFromPixels(st.el);
    }
    const cap = st.captureTarget;
    const pid = e?.pointerId ?? st?.pointerId;
    if (cap != null && pid != null) {
        try {
            cap.releasePointerCapture(pid);
        } catch (_) {}
    }
    dragState = null;
    window.removeEventListener("pointermove", onPointerMove);
    window.removeEventListener("pointerup", onPointerUp);
    window.removeEventListener("pointercancel", onPointerUp);
    if (propsLayoutPanelSyncRaf) {
        cancelAnimationFrame(propsLayoutPanelSyncRaf);
        propsLayoutPanelSyncRaf = 0;
    }
    pendingPropsLayoutNodeId = null;
    clearSnapGuides();
    syncSourceFromModel();
    refreshPropertiesPanel();
}

function syncNodeFromPixels(el) {
    const id = el.dataset.nodeId;
    const node = liveModel.nodes.get(id);
    if (!node) return;
    const parent = el.offsetParent || previewSurface;
    const { w: prW, h: prH } = getParentUdimBasisPx(parent);
    const left = el.offsetLeft;
    const top = el.offsetTop;
    const w = el.offsetWidth;
    const h = el.offsetHeight;
    const ax = node.props.AnchorPoint && node.props.AnchorPoint.type === "vector2" ? node.props.AnchorPoint.x : 0;
    const ay = node.props.AnchorPoint && node.props.AnchorPoint.type === "vector2" ? node.props.AnchorPoint.y : 0;
    const posX = left + ax * w;
    const posY = top + ay * h;
    node.props.Size = {
        type: "udim2",
        xScale: w / prW,
        xOffset: 0,
        yScale: h / prH,
        yOffset: 0
    };
    node.props.Position = {
        type: "udim2",
        xScale: posX / prW,
        xOffset: 0,
        yScale: posY / prH,
        yOffset: 0
    };
    guiLayoutLockedIds.add(id);
}

function luaString(s) {
    return `"${String(s).replace(/\\/g, "\\\\").replace(/"/g, '\\"')}"`;
}

function valueToLuau(val, indent) {
    if (val == null) return "nil";
    if (typeof val === "string") return luaString(val);
    if (typeof val === "number") return String(val);
    if (typeof val === "boolean") return val ? "true" : "false";
    if (typeof val === "object" && val.type === "color3") {
        return `Color3.fromRGB(${val.r}, ${val.g}, ${val.b})`;
    }
    if (typeof val === "object" && val.type === "udim2") {
        const u = val;
        const useScale = u.xOffset === 0 && u.yOffset === 0;
        if (useScale) return `UDim2.fromScale(${fmtNum(u.xScale)}, ${fmtNum(u.yScale)})`;
        return `UDim2.new(${fmtNum(u.xScale)}, ${fmtNum(u.xOffset)}, ${fmtNum(u.yScale)}, ${fmtNum(u.yOffset)})`;
    }
    if (typeof val === "object" && val.type === "udim") {
        return `UDim.new(${fmtNum(val.scale)}, ${fmtNum(val.offset)})`;
    }
    if (typeof val === "object" && val.type === "vector2") {
        return `Vector2.new(${fmtNum(val.x)}, ${fmtNum(val.y)})`;
    }
    if (typeof val === "object" && val.type === "enumPath") {
        return `Enum.${val.path}`;
    }
    if (typeof val === "object" && val.type === "colorSequence" && val.keypoints?.length) {
        const lines = val.keypoints.map(k => `${indent}  ColorSequenceKeypoint.new(${fmtNum(k.time)}, Color3.fromRGB(${k.color[0]}, ${k.color[1]}, ${k.color[2]}))`);
        return `ColorSequence.new({\n${lines.join(",\n")}\n${indent}})`;
    }
    if (typeof val === "object" && val.type === "raw") return val.value;
    return "nil";
}

function fmtNum(n) {
    if (typeof n !== "number" || Number.isNaN(n)) return "0";
    return Number.isInteger(n) ? String(n) : String(Math.round(n * 1e4) / 1e4);
}

const PROP_ORDER = [ "Name", "DisplayOrder", "Size", "Position", "AnchorPoint", "ZIndex", "TridentInputDrag", "Draggable", "BackgroundColor3", "BackgroundTransparency", "BorderSizePixel", "CornerRadius", "Thickness", "Color", "Transparency", "Rotation", "Image", "ScaleType", "Text", "TextColor3", "TextSize", "TextScaled", "TextWrapped", "TextXAlignment", "TextYAlignment", "FillDirection", "HorizontalAlignment", "VerticalAlignment", "Padding", "PaddingTop", "PaddingBottom", "PaddingLeft", "PaddingRight", "CanvasSize", "ScrollBarThickness", "GroupTransparency", "IgnoreGuiInset", "ZIndexBehavior" ];

function parentVarFor(childId, nodesMap) {
    for (const [, n] of nodesMap) {
        if (n.children.includes(childId)) return n.id;
    }
    return null;
}

function supportsAutoUICorner(className) {
    return [ "Frame", "ScrollingFrame", "TextLabel", "TextButton", "TextBox", "ImageLabel", "ImageButton", "CanvasGroup" ].includes(className);
}

function hasUICornerChild(n, nodesMap) {
    for (const cid of n.children || []) {
        if (nodesMap.get(cid)?.className === "UICorner") return true;
    }
    return false;
}

function getExportOpts() {
    const active = document.querySelector("#parentMountBar .parent-mount-btn.active");
    const mount = active?.dataset?.mount || "playerGui";
    return {
        mount: mount,
        playerGui: mount === "playerGui",
        coreGui: mount === "coreGui",
        noParent: mount === "none"
    };
}

function exportToLuau(model, opts = {}) {
    const lines = [];
    const {nodes: nodes, order: order} = model;
    const emitted = new Set;
    let needsUserInputService = false;
    function emitOne(n) {
        if (!n || emitted.has(n.id)) return;
        const p = parentVarFor(n.id, nodes);
        if (p) emitOne(nodes.get(p));
        lines.push(`local ${n.varName} = Instance.new("${n.className}")`);
        const keys = Object.keys(n.props).sort((a, b) => {
            const ia = PROP_ORDER.indexOf(a);
            const ib = PROP_ORDER.indexOf(b);
            if (ia === -1 && ib === -1) return a.localeCompare(b);
            if (ia === -1) return 1;
            if (ib === -1) return -1;
            return ia - ib;
        });
        for (const k of keys) {
            const v = n.props[k];
            if (v === undefined) continue;
            if (k === "TridentInputDrag") continue;
            if (k === "ZIndex" && n.className === "ScreenGui") continue;
            if (k === "Draggable" && (n.props.TridentInputDrag === true || v === false || !supportsDraggableProp(n.className))) continue;
            if (k === "CornerRadius" && n.className !== "UICorner") continue;
            lines.push(`${n.varName}.${k} = ${valueToLuau(v, "  ")}`);
        }
        const par = parentVarFor(n.id, nodes);
        if (par) {
            lines.push(`${n.varName}.Parent = ${nodes.get(par).varName}`);
        }
        const pprops = n.props;
        const crRaw = pprops.CornerRadius?.type === "udim" && Number.isFinite(pprops.CornerRadius.offset) ? pprops.CornerRadius.offset : 0;
        const cornerPx = Math.min(64, Math.max(0, crRaw));
        if (cornerPx > 0 && supportsAutoUICorner(n.className) && !hasUICornerChild(n, nodes)) {
            const c = `${n.varName}_uic`;
            lines.push(`local ${c} = Instance.new("UICorner")`);
            lines.push(`${c}.CornerRadius = UDim.new(0, ${fmtNum(cornerPx)})`);
            lines.push(`${c}.Parent = ${n.varName}`);
        }
        if (n.className === "TextButton" || n.className === "ImageButton") {
            lines.push(`${n.varName}.MouseButton1Click:Connect(function()`);
            lines.push("");
            lines.push("end)");
        }
        if (pprops.TridentInputDrag === true && supportsDraggableProp(n.className)) {
            needsUserInputService = true;
            for (const L of emitInputDragLuauLines(n.varName)) {
                lines.push(L);
            }
        }
        lines.push("");
        emitted.add(n.id);
    }
    for (const id of order) {
        emitOne(nodes.get(id));
    }
    for (const [, n] of nodes) {
        if (!emitted.has(n.id)) emitOne(n);
    }
    let body = lines.join("\n").replace(/\n\n\n+/g, "\n\n").trim();
    const roots = orderedRoots(model);
    const screenGuis = roots.map(id => nodes.get(id)).filter(n => n && n.className === "ScreenGui");
    const head = [];
    if (needsUserInputService) {
        head.push(`local UserInputService = game:GetService("UserInputService")`);
    }
    if (opts.playerGui && screenGuis.length) {
        head.push(`local PlayerGui = game:GetService("Players").LocalPlayer:WaitForChild("PlayerGui")`);
    } else if (opts.coreGui && screenGuis.length) {
        head.push(`local CoreGui = game:GetService("CoreGui")`);
    }
    if (head.length) {
        body = `${head.join("\n\n")}\n\n${body}`;
    }
    if (opts.playerGui && screenGuis.length) {
        for (const sg of screenGuis) {
            body += `\n${sg.varName}.Parent = PlayerGui`;
        }
    } else if (opts.coreGui && screenGuis.length) {
        for (const sg of screenGuis) {
            body += `\n${sg.varName}.Parent = CoreGui`;
        }
    }
    return `${body}\n`;
}

function render() {
    try {
        errorBox.textContent = "";
        const parsed = parseLuau(input.value);
        liveModel = parsed;
        guiLayoutLockedIds.clear();
        liveModel.roots = orderedRoots(liveModel);
        let inited = false;
        if (liveModel.nodes.size === 0) {
            initEmptyDesign();
            inited = true;
        }
        renderFromLiveModel();
        if (inited) syncSourceFromModel();
        const nInst = liveModel.nodes.size;
        const nRoots = liveModel.roots.length;
        setStatus(`Loaded - ${nInst} - ${nRoots}`);
    } catch (err) {
        errorBox.textContent = err.message || String(err);
        setStatus("Parse error");
    }
    schedulePersistEditorState();
}

function downloadLuau() {
    try {
        const text = exportToLuau(liveModel, getExportOpts());
        const blob = new Blob([ text ], {
            type: "text/plain;charset=utf-8"
        });
        const a = document.createElement("a");
        a.href = URL.createObjectURL(blob);
        a.download = "trident-ui.luau";
        a.click();
        URL.revokeObjectURL(a.href);
        setStatus("Downloaded trident-ui.luau");
    } catch (e) {
        errorBox.textContent = e.message || String(e);
    }
}

if (runBtn) runBtn.addEventListener("click", render);

if (loadExampleBtn) {
    loadExampleBtn.addEventListener("click", () => {
        setEditorSourceValue(SAMPLE);
        render();
        schedulePersistEditorState();
    });
}

document.getElementById("saveProjectBtn")?.addEventListener("click", () => {
    try {
        downloadProjectJsonFile();
    } catch (e) {
        errorBox.textContent = e.message || String(e);
    }
});

document.getElementById("loadProjectBtn")?.addEventListener("click", () => {
    document.getElementById("loadProjectFile")?.click();
});

document.getElementById("loadProjectFile")?.addEventListener("change", e => {
    const f = e.target.files?.[0];
    e.target.value = "";
    if (!f) return;
    const reader = new FileReader();
    reader.onload = () => {
        try {
            loadProjectFromJsonText(String(reader.result || ""));
        } catch (err) {
            errorBox.textContent = err.message || String(err);
            setStatus("Could not load project");
        }
    };
    reader.readAsText(f);
});

propsLiveApply?.addEventListener("change", () => schedulePersistEditorState());

if (downloadBtn) downloadBtn.addEventListener("click", downloadLuau);

if (propsApply) {
    propsApply.addEventListener("click", () => {
        if (livePropsDebounce) {
            clearTimeout(livePropsDebounce);
            livePropsDebounce = null;
        }
        propsFormForceFullFormMerge = true;
        applyPropsFromForm();
    });
}

function scheduleLivePropsApply() {
    if (liveApplyingFromForm) return;
    if (!propsLiveApply || !propsLiveApply.checked) return;
    clearTimeout(livePropsDebounce);
    livePropsDebounce = setTimeout(() => {
        livePropsDebounce = null;
        applyPropsFromForm();
    }, 140);
}

if (propsForm) {
    const notePropsLayoutTouch = e => {
        if (!e.isTrusted) return;
        const id = e.target?.id;
        if (id && PROPS_LAYOUT_FIELD_IDS.has(id)) propsFormLayoutFieldsTouched = true;
    };
    propsForm.addEventListener("input", e => {
        notePropsLayoutTouch(e);
        scheduleLivePropsApply();
    });
    propsForm.addEventListener("change", e => {
        notePropsLayoutTouch(e);
        scheduleLivePropsApply();
    });
}

function unlockGuiLayoutFromFormInputs() {
    if (suppressLayoutUnlockFromPropsRefresh) return;
    guiLayoutLockedIds.clear();
}

for (const id of [ "propsSizeX", "propsSizeY", "propsPosX", "propsPosY", "propsAx", "propsAy" ]) {
    const el = document.getElementById(id);
    if (!el) continue;
    el.addEventListener("input", unlockGuiLayoutFromFormInputs);
    el.addEventListener("change", unlockGuiLayoutFromFormInputs);
    el.addEventListener("wheel", e => {
        e.preventDefault();
    }, {
        passive: false
    });
}

if (propsDelete) {
    propsDelete.addEventListener("click", () => {
        if (selectedNodeIds.size) deleteSelection();
    });
}

document.getElementById("parentMountBar")?.addEventListener("click", e => {
    const b = e.target.closest(".parent-mount-btn");
    if (!b) return;
    document.querySelectorAll("#parentMountBar .parent-mount-btn").forEach(x => x.classList.remove("active"));
    b.classList.add("active");
    if (liveModel?.nodes?.size) syncSourceFromModel();
    schedulePersistEditorState();
});

/** Do not auto-parse the source on every keystroke. Debounced `render()` was re-parsing `input.value` and replacing `liveModel`, which fought `syncSourceFromModel()` (preview edits, resize, props) and could drop `Size` / revert to defaults — labels “jumping” huge. Use the Refresh control to parse Luau from the editor. */

const toolboxEl = document.getElementById("toolbox");

if (toolboxEl) {
    toolboxEl.addEventListener("click", e => {
        const chip = e.target.closest("[data-insert]");
        if (!chip) return;
        insertInstance(chip.getAttribute("data-insert"), null);
    });
    toolboxEl.querySelectorAll("[data-insert]").forEach(chip => {
        chip.addEventListener("dragstart", e => {
            e.dataTransfer.setData("application/x-trident-class", chip.getAttribute("data-insert") || "");
            e.dataTransfer.effectAllowed = "copy";
        });
    });
}

document.getElementById("propsMakeDraggableBtn")?.addEventListener("click", () => applyDraggableExportToSelection(true));
document.getElementById("propsClearDraggableBtn")?.addEventListener("click", () => applyDraggableExportToSelection(false));

function initMobileShell() {
    const split = document.getElementById("mainSplit");
    const bar = document.getElementById("mobileTabBar");
    if (!split || !bar) return;
    const mq = window.matchMedia("(max-width: 720px)");
    const btns = Array.from(bar.querySelectorAll(".mobile-tab-btn"));
    const validPanes = new Set([ "insert", "source", "preview", "props" ]);

    function syncTabButtons(pane) {
        btns.forEach(b => {
            const active = b.getAttribute("data-mobile-pane") === pane;
            b.setAttribute("aria-current", active ? "true" : "false");
        });
    }

    function apply() {
        if (mq.matches) {
            bar.removeAttribute("hidden");
            let pane = split.getAttribute("data-mobile-pane") || "preview";
            if (!validPanes.has(pane)) pane = "preview";
            split.setAttribute("data-mobile-pane", pane);
            syncTabButtons(pane);
        } else {
            bar.setAttribute("hidden", "");
            split.removeAttribute("data-mobile-pane");
        }
    }

    btns.forEach(b => {
        b.addEventListener("click", () => {
            const pane = b.getAttribute("data-mobile-pane");
            if (!pane || !validPanes.has(pane)) return;
            split.setAttribute("data-mobile-pane", pane);
            syncTabButtons(pane);
        });
    });

    mq.addEventListener("change", apply);
    apply();
}

function shouldBlockDeleteSelectionShortcut() {
    const a = document.activeElement;
    if (!a) return false;
    if (a.id === "input") return true;
    if (a.isContentEditable) return true;
    if (a.closest?.("#propsColumn") && a.matches("input, textarea, select")) return true;
    if (previewSurface?.contains(a) && a.tagName === "TEXTAREA" && a.dataset?.className === "TextBox") return true;
    return false;
}

/** Let Source / property text fields use native ⌘C / ⌘V for text. */
function shouldUseNativeClipboardInTarget() {
    const a = document.activeElement;
    if (!a) return false;
    if (a.id === "input") return true;
    if (a.isContentEditable) return true;
    if (a.closest?.("#propsColumn") && a.matches("input, textarea, select")) return true;
    if (previewSurface?.contains(a) && a.tagName === "TEXTAREA" && a.dataset?.className === "TextBox") return true;
    return false;
}

document.addEventListener("keydown", e => {
    const mod = e.metaKey || e.ctrlKey;
    if (mod && (e.key === "c" || e.key === "C")) {
        if (shouldUseNativeClipboardInTarget()) return;
        e.preventDefault();
        copyTridentSelection();
        return;
    }
    if (mod && (e.key === "v" || e.key === "V")) {
        if (shouldUseNativeClipboardInTarget()) return;
        e.preventDefault();
        pasteTridentClipboard();
        return;
    }
    if (mod && e.key === "z") {
        if (e.target?.id === "input") return;
        e.preventDefault();
        if (e.shiftKey) performRedo(); else performUndo();
        return;
    }
    if (mod && (e.key === "y" || e.key === "Y")) {
        if (e.target?.id === "input") return;
        e.preventDefault();
        performRedo();
        return;
    }
    if (e.key !== "Backspace" && e.key !== "Delete") return;
    if (shouldBlockDeleteSelectionShortcut()) return;
    if (selectedNodeIds.size === 0) return;
    e.preventDefault();
    deleteSelection();
}, true);

installBgColorPicker();
initMobileShell();

for (const id of [ "propsBgR", "propsBgG", "propsBgB" ]) {
    document.getElementById(id)?.addEventListener("input", () => updateBgColorPickerUI());
}

try {
    const raw = localStorage.getItem(TRIDENT_STORAGE_KEY);
    if (raw) {
        const snap = JSON.parse(raw);
        if (snap && typeof snap.source === "string" && snap.source.trim() !== "") {
            applyEditorSnapshot(snap);
        } else if (input && !input.value.trim()) {
            setEditorSourceValue(SAMPLE);
        }
    } else if (input && !input.value.trim()) {
        setEditorSourceValue(SAMPLE);
    }
} catch (_) {
    if (input && !input.value.trim()) setEditorSourceValue(SAMPLE);
}

/* ── Column resizers ─────────────────────────────────────────── */
(function initColumnResizers() {
    const split = document.getElementById("mainSplit");
    if (!split) return;
    split.querySelectorAll(".col-resizer").forEach(handle => {
        handle.addEventListener("pointerdown", e => {
            e.preventDefault();
            handle.classList.add("active");
            handle.setPointerCapture(e.pointerId);
            const startX = e.clientX;

            const leftId = handle.dataset.resizeLeft;
            const rightId = handle.dataset.resizeRight;
            const leftFlexCls = handle.dataset.resizeLeftFlex;
            const rightFlexCls = handle.dataset.resizeRightFlex;

            let leftEl = leftId ? document.getElementById(leftId) : null;
            let rightEl = rightId ? document.getElementById(rightId) : null;
            if (leftFlexCls) leftEl = split.querySelector("." + leftFlexCls);
            if (rightFlexCls) rightEl = split.querySelector("." + rightFlexCls);

            const leftW0 = leftEl ? leftEl.getBoundingClientRect().width : 0;
            const rightW0 = rightEl ? rightEl.getBoundingClientRect().width : 0;

            const onMove = ev => {
                const dx = ev.clientX - startX;
                if (leftEl) {
                    const nw = Math.max(100, leftW0 + dx);
                    if (leftFlexCls) {
                        leftEl.style.flex = "0 0 " + nw + "px";
                    } else {
                        leftEl.style.width = nw + "px";
                    }
                }
                if (rightEl) {
                    const nw = Math.max(100, rightW0 - dx);
                    if (rightFlexCls) {
                        rightEl.style.flex = "0 0 " + nw + "px";
                    } else {
                        rightEl.style.width = nw + "px";
                    }
                }
            };
            const onUp = () => {
                handle.classList.remove("active");
                window.removeEventListener("pointermove", onMove);
                window.removeEventListener("pointerup", onUp);
            };
            window.addEventListener("pointermove", onMove);
            window.addEventListener("pointerup", onUp);
        });
    });
})();

/* ── Preview size label ──────────────────────────────────────── */
(function initPreviewSizeLabel() {
    const surf = document.getElementById("previewSurface");
    const lbl = document.getElementById("previewSizeLabel");
    if (!surf || !lbl) return;
    function update() {
        const w = Math.round(surf.clientWidth);
        const h = Math.round(surf.clientHeight);
        lbl.textContent = w + " × " + h;
    }
    update();
    if (typeof ResizeObserver !== "undefined") {
        new ResizeObserver(update).observe(surf);
    }
})();

render();