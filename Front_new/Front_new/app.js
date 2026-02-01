const state = {
  data: [],
  selected: 0,
  filePath: "",
  customMacros: ""
};

const STORAGE_KEY = "ra-json-editor-v12-deps-append";

const el = {
  filePath: document.getElementById("file-path"),
  loadFile: document.getElementById("load-file"),
  saveFile: document.getElementById("save-file"),
  newFile: document.getElementById("new-file"),
  filePicker: document.getElementById("file-picker"),
  
  addEntry: document.getElementById("add-entry"),
  insertEntry: document.getElementById("insert-entry"),
  autoRenumber: document.getElementById("auto-renumber"),
  
  // New Buttons
  btnAppendDeps: document.getElementById("btn-append-deps"),
  btnUndoDeps: document.getElementById("btn-undo-deps"),

  openBatchModal: document.getElementById("open-batch-modal"),
  openMacroModal: document.getElementById("open-macro-modal"),
  
  moveUp: document.getElementById("move-up"),
  moveDown: document.getElementById("move-down"),
  deleteEntry: document.getElementById("delete-entry"),
  entryList: document.getElementById("entry-list"),
  editorForm: document.getElementById("editor-form"),
  
  preview: document.getElementById("preview"),
  previewMeta: document.getElementById("preview-meta"),
  scanRefs: document.getElementById("scan-refs"),

  status: document.getElementById("status"),
  rawJson: document.getElementById("raw-json"),
  applyRaw: document.getElementById("apply-raw"),
  formatRaw: document.getElementById("format-raw"),

  // Modals
  batchModal: document.getElementById("batch-modal"),
  batchStart: document.getElementById("batch-start"),
  batchEnd: document.getElementById("batch-end"),
  batchApply: document.getElementById("batch-apply"),
  batchCancel: document.getElementById("batch-cancel"),

  macroModal: document.getElementById("macro-modal"),
  macroInput: document.getElementById("macro-input"),
  macroSave: document.getElementById("macro-save"),
  macroCancel: document.getElementById("macro-cancel"),
};

// 标准数据结构模板
const defaultEntry = () => ({
  label: "",
  env: "thm",
  number_components: [1],
  extracted_labels: [],
  context: {
    chapter: "",
    section: "",
    subsection: "",
    chapter_number: null,
    section_number: "",
    subsection_number: "",
  },
  content: "",
  dependencies: [],
  proof: "",
});

const setStatus = (message, kind = "info") => {
  el.status.textContent = message;
  el.status.style.color = kind === "error" ? "#c24c3d" : "#d17b22";
};

// --- Logic Helpers ---

const checkDuplicateLabels = () => {
  const labelPositions = {};
  state.data.forEach((item, idx) => {
    if (item && item.label) {
      if (!labelPositions[item.label]) labelPositions[item.label] = [];
      labelPositions[item.label].push(idx + 1);
    }
  });

  const listItems = el.entryList.children;
  let hasDup = false;
  const conflictDetails = [];

  for (let i = 0; i < listItems.length; i++) {
    const item = state.data[i];
    if (item && item.label && labelPositions[item.label].length > 1) {
      listItems[i].classList.add("error");
      hasDup = true;
    } else {
      if(listItems[i]) listItems[i].classList.remove("error");
    }
  }
  
  if (hasDup) {
    for (const [lbl, indices] of Object.entries(labelPositions)) {
      if (indices.length > 1) {
        conflictDetails.push(`${lbl} (条目 ${indices.join(", ")})`);
      }
    }
    const msg = conflictDetails.slice(0, 3).join("; ") + (conflictDetails.length > 3 ? "..." : "");
    setStatus(`警告：Label 冲突: ${msg}`, "error");
  }
};

const autoRenumber = () => {
  const toShortMap = {
    "theorem": "thm", "thm": "thm",
    "lemma": "lem", "lem": "lem",
    "proposition": "prop", "prop": "prop",
    "corollary": "cor", "cor": "cor",
    "definition": "def", "defn": "def", "def": "def",
    "remark": "rem", "rem": "rem",
    "example": "exam", "exam": "exam",
    "conjecture": "conj", "conj": "conj",
    "problem": "prob", "prob": "prob",
    "algorithm": "algo", "algo": "algo",
    "assumption": "assum", "assum": "assum",
    "axiom": "ax", "ax": "ax",
    "fact": "fact"
  };

  const shortToFull = {
    "thm": "Theorem", "lem": "Lemma", "prop": "Proposition",
    "cor": "Corollary", "def": "Definition", "rem": "Remark",
    "exam": "Example", "conj": "Conjecture", "prob": "Problem",
    "algo": "Algorithm", "assum": "Assumption", "ax": "Axiom",
    "fact": "Fact"
  };

  const labelMapping = {}; 
  const counters = {};
  let fixCount = 0;

  state.data.forEach(item => {
    if (!item.env) return;

    const rawEnv = item.env.toLowerCase().trim();
    const shortEnv = toShortMap[rawEnv] || rawEnv;
    item.env = shortEnv;

    if (!item.context) item.context = {};

    let secVal = item.context.section_number;
    if (secVal && String(secVal).includes('.')) {
        const parts = String(secVal).split('.');
        if (parts.length >= 2) {
            item.context.section_number = Number(parts[0]);
            item.context.subsection_number = Number(parts[1]);
            fixCount++;
        }
    }

    const chNum = parseFloat(item.context.chapter_number);
    const secNum = parseFloat(item.context.section_number);
    const subNum = parseFloat(item.context.subsection_number);
    const isValid = (n) => !isNaN(n);

    const contextKey = `${shortEnv}|${isValid(chNum)?chNum:''}|${isValid(secNum)?secNum:''}|${isValid(subNum)?subNum:''}`;
    
    if (!counters[contextKey]) counters[contextKey] = 0;
    counters[contextKey]++;
    const localCount = counters[contextKey];

    const comps = [];
    if (isValid(chNum)) comps.push(chNum);
    if (isValid(secNum)) comps.push(secNum);
    if (isValid(subNum)) comps.push(subNum);
    comps.push(localCount);

    const displayEnv = shortToFull[shortEnv] || (shortEnv.charAt(0).toUpperCase() + shortEnv.slice(1));
    const numberString = comps.join(".");
    const newLabel = `${displayEnv} ${numberString}`;

    if (item.label) labelMapping[item.label] = newLabel;

    item.temp_new_label = newLabel;
    item.temp_new_comps = comps;
  });

  let depUpdatesCount = 0;
  state.data.forEach(item => {
    if (item.dependencies && Array.isArray(item.dependencies)) {
      item.dependencies = item.dependencies.map(dep => {
        if (labelMapping[dep] && labelMapping[dep] !== dep) {
          depUpdatesCount++;
          return labelMapping[dep];
        }
        return dep;
      });
      item.dependencies = [...new Set(item.dependencies)];
    }

    if (item.temp_new_label) {
      item.label = item.temp_new_label;
      item.number_components = item.temp_new_comps;
      delete item.temp_new_label;
      delete item.temp_new_comps;
    }
  });
  
  saveDraft();
  render();
  let msg = `已重新编号`;
  if(fixCount > 0) msg += ` (修复 ${fixCount} 处 section 拆分)`;
  if(depUpdatesCount > 0) msg += ` (更新 ${depUpdatesCount} 处引用)`;
  setStatus(msg);
};

// --- New Features: Append / Undo Dependencies ---

const appendDeps = () => {
  if (!confirm("确定要将 Dependencies 列表追加到 Content 字段末尾吗？")) return;
  
  let count = 0;
  state.data.forEach(item => {
    if (item.dependencies && Array.isArray(item.dependencies) && item.dependencies.length > 0) {
      // Create the string: (depend on: "Dep 1", "Dep 2")
      const depStr = item.dependencies.map(d => `"${d}"`).join(', ');
      const suffix = `\n(depend on: ${depStr})`;
      
      // Prevent duplicates if already ends with this
      if (!item.content.trimEnd().endsWith(suffix.trim())) {
        item.content = (item.content || "") + suffix;
        count++;
      }
    }
  });

  saveDraft();
  render();
  setStatus(`已追加依赖信息到 ${count} 个条目`);
};

const undoAppendDeps = () => {
  if (!confirm("确定要撤销追加的依赖信息吗？(将删除 content 末尾的 match 文本)")) return;

  let count = 0;
  // Regex to match the appended format at the end of the string
  // Matches: \n(depend on: "...")  End of String
  const regex = /\n\(depend on: .*\)$/;

  state.data.forEach(item => {
    if (item.content && regex.test(item.content)) {
      item.content = item.content.replace(regex, "");
      count++;
    }
  });

  saveDraft();
  render();
  setStatus(`已撤销 ${count} 个条目的依赖追加`);
};

const normalizeData = (data) => {
  const template = defaultEntry();
  return data.map(item => {
    const merged = { ...template, ...item };
    merged.context = { ...template.context, ...(item.context || {}) };
    if (!Array.isArray(merged.number_components)) merged.number_components = [];
    if (!Array.isArray(merged.dependencies)) merged.dependencies = [];
    if (!Array.isArray(merged.extracted_labels)) merged.extracted_labels = [];
    if (merged.context.subsection === undefined) merged.context.subsection = "";
    if (merged.context.subsection_number === undefined) merged.context.subsection_number = "";
    return merged;
  });
};

const findTransitiveDependencies = (startLabel, visited = new Set()) => {
  if (visited.has(startLabel)) return [];
  visited.add(startLabel);
  const target = state.data.find(d => d.label === startLabel);
  if (!target) return [startLabel];
  let deps = [startLabel];
  if (target.dependencies && Array.isArray(target.dependencies)) {
    target.dependencies.forEach(dep => {
      deps = deps.concat(findTransitiveDependencies(dep, visited));
    });
  }
  return deps;
};

const extractLabelsFromText = (text) => {
  if (!text) return [];
  const regex = /\\label\{([^}]+)\}/g;
  const found = [];
  let m;
  while ((m = regex.exec(text)) !== null) {
    found.push(m[1]);
  }
  return found;
};

const scanRefsAndLink = () => {
  const labelToItemIndex = {};
  state.data.forEach((item, idx) => {
    const labels = [
      ...extractLabelsFromText(item.content),
      ...extractLabelsFromText(item.proof)
    ];
    item.extracted_labels = [...new Set(labels)];
    item.extracted_labels.forEach(lab => {
      labelToItemIndex[lab] = idx;
    });
  });

  let linksAdded = 0;
  const refRegex = /\\(c?ref|hyperref|eqref)\[?.*?\]?\{([^}]+)\}/g;

  state.data.forEach((item) => {
    const text = (item.content || "") + (item.proof || "");
    let m;
    const newDeps = new Set(item.dependencies || []);
    while ((m = refRegex.exec(text)) !== null) {
      const refKey = m[2];
      if (labelToItemIndex.hasOwnProperty(refKey)) {
        const ownerIdx = labelToItemIndex[refKey];
        const ownerLabel = state.data[ownerIdx].label;
        if (ownerLabel && ownerLabel !== item.label) {
           if (!newDeps.has(ownerLabel)) {
             newDeps.add(ownerLabel);
             linksAdded++;
           }
        }
      }
    }
    item.dependencies = Array.from(newDeps);
  });

  saveDraft();
  render();
  setStatus(`扫描完成，新增 ${linksAdded} 个关联`);
};

const convertLatexLists = (text) => {
  let out = text;
  const listRegex = /\\begin\{(enumerate|itemize|description)\}((?:(?!\\begin\{(?:enumerate|itemize|description)\})[\s\S])*?)\\end\{\1\}/g;
  let matchFound = true;
  while (matchFound) {
    matchFound = false;
    out = out.replace(listRegex, (match, type, body) => {
      matchFound = true;
      let cleanBody = body.replace(/\\item\s*\[([^\]]*)\]/g, '\n- **$1** ');
      const replacement = type === 'enumerate' ? '\n1. ' : '\n- ';
      cleanBody = cleanBody.replace(/\\item/g, replacement);
      return '\n' + cleanBody + '\n';
    });
  }
  return out;
};

const processLatexToHtml = (text, envName) => {
  if (!text) return "";
  let out = text;
  const mathStore = [];
  
  out = out.replace(/^\s*\\begin\{[^}]+\}(\[[^\]]*\])?/g, "");
  out = out.replace(/\\end\{[^}]+\}\s*$/g, "");
  out = out.replace(/\\label\{[^}]+\}/g, "");
  
  const pushMath = (latex, isDisplay) => {
      const index = mathStore.length;
      mathStore.push({ latex, isDisplay });
      return `@@MATH_${index}@@`;
  };

  out = out.replace(/\\begin\{(equation|align|gather|flalign|alignat)\*?\}([\s\S]*?)\\end\{\1\*?\}/g, 
    (match, env, body) => pushMath(`\\begin{${env}*}${body}\\end{${env}*}`, true));
  out = out.replace(/\\\[([\s\S]*?)\\\]/g, (match, body) => pushMath(body, true));
  out = out.replace(/\$\$([\s\S]*?)\$\$/g, (match, body) => pushMath(body, true));
  out = out.replace(/\\\(([\s\S]*?)\\\)/g, (match, body) => pushMath(body, false));
  out = out.replace(/(?<!\\)\$([^$]+?)(?<!\\)\$/g, (match, body) => pushMath(body, false));

  out = convertLatexLists(out);

  out = out.replace(/\\(emph|textit)\{((?:[^{}]|\\\{|\\\})*)\}/g, '*$2*');
  out = out.replace(/\\textbf\{((?:[^{}]|\\\{|\\\})*)\}/g, '**$1**');
  out = out.replace(/\\texttt\{((?:[^{}]|\\\{|\\\})*)\}/g, '`$1`');
  out = out.replace(/\\(c?ref|eqref|cite)\{([^}]+)\}/g, ' **$2** '); 
  out = out.replace(/\\hyperref\[(.*?)\]\{(.*?)\}/g, '$2');

  let html = marked.parse(out);

  html = html.replace(/@@MATH_(\d+)@@/g, (match, index) => {
      const entry = mathStore[parseInt(index)];
      if (!entry) return "";
      if (entry.isDisplay) {
          return `\\[${entry.latex}\\]`;
      } else {
          return `\\(${entry.latex}\\)`;
      }
  });

  return html;
};

// --- Core App & Rendering ---

const refreshIndexes = () => {
  state.data.forEach((item, idx) => {
    item.index = idx + 1;
  });
};

const saveDraft = () => {
  refreshIndexes();
  const payload = {
    filePath: state.filePath,
    data: state.data,
    selected: state.selected,
    customMacros: state.customMacros
  };
  localStorage.setItem(STORAGE_KEY, JSON.stringify(payload));
};

const loadDraft = () => {
  const raw = localStorage.getItem(STORAGE_KEY);
  if (!raw) return false;
  try {
    const payload = JSON.parse(raw);
    if (Array.isArray(payload.data)) {
      state.data = payload.data;
      state.selected = payload.selected || 0;
      state.filePath = payload.filePath || "";
      state.customMacros = payload.customMacros || "";
      el.filePath.value = state.filePath;
      setStatus("已加载草稿");
      return true;
    }
  } catch { return false; }
  return false;
};

const renderList = () => {
  el.entryList.innerHTML = "";
  state.data.forEach((item, idx) => {
    const div = document.createElement("div");
    div.className = "entry-item" + (idx === state.selected ? " active" : "");
    const label = item.label ? ` ${item.label}` : " (无 Label)";
    div.textContent = `${idx + 1}. ${label}`;
    div.addEventListener("click", () => {
      state.selected = idx;
      render();
    });
    el.entryList.appendChild(div);
  });
  checkDuplicateLabels();
};

const renderForm = () => {
  const item = state.data[state.selected];
  if (!item) {
    el.editorForm.innerHTML = "<p>暂无条目，请点击“新增”或“插入”。</p>";
    return;
  }
  const v = (val) => (val === undefined || val === null) ? "" : val;

  el.editorForm.innerHTML = `
    <div class="field-row">
      <label class="field" style="flex:2">
        <span>Label (唯一标识)</span>
        <input id="field-label" type="text" value="${v(item.label)}" />
      </label>
      <label class="field" style="flex:1">
        <span>Env</span>
        <input id="field-env" type="text" value="${v(item.env)}" />
      </label>
    </div>
    <label class="field">
      <span>Number Components</span>
      <input id="field-number-components" type="text" value="${(item.number_components || []).join(", ")}" />
    </label>
    <fieldset class="field">
      <legend>Context</legend>
      <div class="field-row">
        <div class="field"><span>Chapter</span><input id="field-context-chapter" type="text" value="${v(item.context?.chapter)}" /></div>
        <div class="field"><span>Chap Num</span><input id="field-context-chapter-number" type="number" value="${v(item.context?.chapter_number)}" /></div>
      </div>
      <div class="field-row">
        <div class="field"><span>Section</span><input id="field-context-section" type="text" value="${v(item.context?.section)}" /></div>
        <div class="field"><span>Sec Num</span><input id="field-context-section-number" type="text" value="${v(item.context?.section_number)}" /></div>
      </div>
      <div class="field-row">
        <div class="field"><span>Subsection</span><input id="field-context-subsection" type="text" value="${v(item.context?.subsection)}" /></div>
        <div class="field"><span>Subsec Num</span><input id="field-context-subsection-number" type="text" value="${v(item.context?.subsection_number)}" /></div>
      </div>
    </fieldset>
    <label class="field"><span>Dependencies</span><textarea id="field-dependencies">${(item.dependencies || []).join("\n")}</textarea></label>
    <label class="field"><span>Content</span><textarea id="field-content" spellcheck="false"></textarea></label>
    <label class="field"><span>Proof</span><textarea id="field-proof" spellcheck="false"></textarea></label>
    <div class="field"><span>Extracted Internal Labels</span><div style="font-size:12px; color:#888; padding:4px;">${(item.extracted_labels||[]).join(", ")}</div></div>
  `;

  document.getElementById("field-content").value = item.content || "";
  document.getElementById("field-proof").value = item.proof || "";

  const bind = (id, setter) => {
    const elInput = document.getElementById(id);
    if(!elInput) return;
    elInput.addEventListener("input", (e) => {
      setter(e.target.value);
      saveDraft();
    });
    if(id === "field-label") {
        elInput.addEventListener("input", () => { renderList(); }); 
        elInput.addEventListener("input", () => { renderPreview(); });
    }
    if(id === "field-env") elInput.addEventListener("input", () => { renderPreview(); });
  };
  
  const bindClean = (id, key) => {
    const elInput = document.getElementById(id);
    if(!elInput) return;
    elInput.addEventListener("input", (e) => {
      item[key] = e.target.value;
      renderPreview();
      saveDraft();
    });
    elInput.addEventListener("blur", (e) => {
      const val = e.target.value;
      if (val.includes("\\\\")) {
        let cleaned = val.replace(/\\\\(begin|end|label|ref|cite|eqref)/g, "\\$1");
        if (cleaned !== val) {
            item[key] = cleaned;
            e.target.value = cleaned;
            renderPreview();
            saveDraft();
            setStatus("已自动修正多余的转义字符");
        }
      }
    });
  };

  bind("field-label", v => item.label = v);
  bind("field-env", v => item.env = v);
  bind("field-number-components", v => item.number_components = v.split(",").map(s => s.trim()).filter(s=>s).map(Number));
  
  if (!item.context) item.context = {};
  bind("field-context-chapter", v => item.context.chapter = v);
  bind("field-context-section", v => item.context.section = v);
  bind("field-context-subsection", v => item.context.subsection = v);
  bind("field-context-chapter-number", v => item.context.chapter_number = v ? Number(v) : null);
  bind("field-context-section-number", v => item.context.section_number = v);
  bind("field-context-subsection-number", v => item.context.subsection_number = v);

  const depEl = document.getElementById("field-dependencies");
  if(depEl) {
    depEl.addEventListener("change", (e) => {
       const rawLines = e.target.value.split("\n").map(s => s.trim()).filter(s => s);
       let finalDeps = new Set();
       rawLines.forEach(lbl => {
          const chain = findTransitiveDependencies(lbl);
          chain.forEach(c => finalDeps.add(c));
       });
       item.dependencies = Array.from(finalDeps);
       e.target.value = item.dependencies.join("\n");
       saveDraft();
       renderPreview();
    });
  }

  bindClean("field-content", "content");
  bindClean("field-proof", "proof");
};

const renderPreview = () => {
  const item = state.data[state.selected];
  const macros = state.customMacros || "";
  const macroHtml = macros ? `<div style="display:none">$$ ${macros} $$</div>` : "";

  if (!item) {
    el.preview.innerHTML = macroHtml + "<p class='meta'>暂无内容</p>";
    el.previewMeta.textContent = "";
    return;
  }

  const metaParts = [];
  if (item.env) metaParts.push(`**${item.env}**`);
  if (item.context?.chapter) metaParts.push(`Ch:${item.context.chapter}`);
  if (item.context?.section) metaParts.push(`Sec:${item.context.section}`);
  el.previewMeta.innerHTML = metaParts.join(" &middot; ");

  el.preview.innerHTML = "";
  const wrapper = document.createElement("div");
  wrapper.innerHTML = macroHtml;
  el.preview.appendChild(wrapper);

  const h1 = document.createElement("h1");
  h1.textContent = item.label || "Untitled";
  el.preview.appendChild(h1);

  if (item.content) {
      const h3 = document.createElement("h3");
      h3.textContent = "Content";
      el.preview.appendChild(h3);
      const div = document.createElement("div");
      div.innerHTML = processLatexToHtml(item.content, item.env);
      el.preview.appendChild(div);
  }
  
  if (item.proof) {
      const h3 = document.createElement("h3");
      h3.textContent = "Proof";
      el.preview.appendChild(h3);
      const div = document.createElement("div");
      div.innerHTML = processLatexToHtml(item.proof, "proof");
      el.preview.appendChild(div);
  }
  
  if (item.dependencies && item.dependencies.length) {
      const h3 = document.createElement("h3");
      h3.textContent = "Dependencies";
      el.preview.appendChild(h3);
      const ul = document.createElement("ul");
      item.dependencies.forEach(d => {
          const li = document.createElement("li");
          li.textContent = d;
          ul.appendChild(li);
      });
      el.preview.appendChild(ul);
  }

  if (window.MathJax && window.MathJax.typesetPromise) {
    window.MathJax.typesetPromise([el.preview]).catch(err => console.log(err));
  }
};

const renderRaw = () => {
  if (document.activeElement === el.rawJson) return;
  el.rawJson.value = JSON.stringify(state.data, null, 2);
};

const render = () => {
  try {
    refreshIndexes();
    renderList();
    renderForm();
    renderPreview();
    renderRaw();
  } catch (e) {
    console.error(e);
    setStatus("渲染错误: " + e.message, "error");
  }
};

// --- Actions ---

el.newFile.addEventListener("click", () => {
    if(!confirm("确定要新建吗？未保存的内容将丢失。")) return;
    state.data = [defaultEntry()];
    state.selected = 0;
    saveDraft();
    render();
    setStatus("已新建空白文件");
});

el.insertEntry.addEventListener("click", () => {
    const insertIndex = state.selected + 1;
    state.data.splice(insertIndex, 0, defaultEntry());
    state.selected = insertIndex;
    saveDraft();
    render();
    setStatus("已插入新条目");
});

el.addEntry.addEventListener("click", () => {
    state.data.push(defaultEntry());
    state.selected = state.data.length - 1;
    saveDraft();
    render();
});

el.deleteEntry.addEventListener("click", () => {
    if(state.data.length === 0) return;
    state.data.splice(state.selected, 1);
    state.selected = Math.min(state.selected, Math.max(0, state.data.length - 1));
    saveDraft();
    render();
});

el.moveUp.addEventListener("click", () => {
    if (state.selected > 0) {
        const item = state.data.splice(state.selected, 1)[0];
        state.selected--;
        state.data.splice(state.selected, 0, item);
        saveDraft();
        render();
    }
});
el.moveDown.addEventListener("click", () => {
    if (state.selected < state.data.length - 1) {
        const item = state.data.splice(state.selected, 1)[0];
        state.selected++;
        state.data.splice(state.selected, 0, item);
        saveDraft();
        render();
    }
});

// Append / Undo Listeners
el.btnAppendDeps.addEventListener("click", appendDeps);
el.btnUndoDeps.addEventListener("click", undoAppendDeps);

el.openBatchModal.addEventListener("click", () => {
  el.batchModal.classList.remove("hidden");
  el.batchStart.value = state.selected + 1;
  el.batchEnd.value = state.data.length;
});
el.batchCancel.addEventListener("click", () => { el.batchModal.classList.add("hidden"); });
el.batchApply.addEventListener("click", () => {
  const start = parseInt(el.batchStart.value) - 1;
  const end = parseInt(el.batchEnd.value) - 1;
  if (isNaN(start) || isNaN(end) || start < 0 || end >= state.data.length || start > end) {
    alert("索引无效"); return;
  }
  const updates = {};
  const getVal = (id) => document.getElementById(id).value.trim();
  const ch = getVal("batch-chapter"); if(ch) updates.chapter = ch;
  const sec = getVal("batch-section"); if(sec) updates.section = sec;
  const sub = getVal("batch-subsection"); if(sub) updates.subsection = sub;
  const chn = getVal("batch-chapter-number"); if(chn) updates.chapter_number = Number(chn);
  const sen = getVal("batch-section-number"); if(sen) updates.section_number = sen;
  const subn = getVal("batch-subsection-number"); if(subn) updates.subsection_number = subn;
  
  for (let i = start; i <= end; i++) {
    if (!state.data[i].context) state.data[i].context = {};
    Object.assign(state.data[i].context, updates);
  }
  el.batchModal.classList.add("hidden");
  saveDraft();
  render();
  setStatus(`批量修改了 ${end - start + 1} 条`);
});

el.openMacroModal.addEventListener("click", () => {
  el.macroModal.classList.remove("hidden");
  el.macroInput.value = state.customMacros || "";
});
el.macroCancel.addEventListener("click", () => { el.macroModal.classList.add("hidden"); });
el.macroSave.addEventListener("click", () => {
  state.customMacros = el.macroInput.value;
  el.macroModal.classList.add("hidden");
  saveDraft();
  render();
});

el.autoRenumber.addEventListener("click", () => {
  if(confirm("确定要重新编号所有条目吗？\n1. Section 号若含点（如 1.1）将自动拆分\n2. Env 将转换为缩写\n3. 依赖引用将自动更新")) {
    autoRenumber();
  }
});
el.scanRefs.addEventListener("click", scanRefsAndLink);

const loadFromPath = async (path) => {
  setStatus("加载中...");
  try {
    const response = await fetch(path);
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    state.data = await response.json();
    state.selected = 0; state.filePath = path;
    saveDraft(); render(); setStatus("加载完成");
  } catch (error) { setStatus(`加载失败：${error.message}`, "error"); }
};

el.loadFile.addEventListener("click", () => { if(el.filePath.value.trim()) loadFromPath(el.filePath.value.trim()); });

el.filePicker.addEventListener("change", (e) => {
  const file = e.target.files?.[0]; if (!file) return;
  const reader = new FileReader();
  reader.onload = () => {
    try {
      const raw = reader.result;
      const clean = raw.replace(/\u00A0/g, " ");
      state.data = JSON.parse(clean);
      state.selected = 0; 
      state.filePath = file.name; 
      saveDraft(); 
      render(); 
      setStatus("已读取本地文件");
    } catch(err) { 
      console.error(err);
      setStatus("JSON 解析失败: " + err.message, "error"); 
    }
    el.filePicker.value = "";
  };
  reader.readAsText(file);
});

el.saveFile.addEventListener("click", () => {
  const exportData = normalizeData(state.data);
  const blob = new Blob([JSON.stringify(exportData, null, 2)], { type: "application/json" });
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.href = url; link.download = (state.filePath.split("/").pop() || "data.json");
  document.body.appendChild(link); link.click(); document.body.removeChild(link);
});

el.applyRaw.addEventListener("click", () => { try { state.data = JSON.parse(el.rawJson.value); state.selected = 0; saveDraft(); render(); setStatus("Raw Applied"); } catch(e) { setStatus(e.message, "error"); } });
el.formatRaw.addEventListener("click", () => { try { const d = JSON.parse(el.rawJson.value); el.rawJson.value = JSON.stringify(d, null, 2); } catch(e){} });

const init = () => { loadDraft(); render(); };
init();