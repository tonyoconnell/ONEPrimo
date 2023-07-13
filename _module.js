function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link0;
	let link1;
	let link2;
	let link3;
	let link3_href_value;
	let style;
	let t;

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link0 = element("link");
			link1 = element("link");
			link2 = element("link");
			link3 = element("link");
			style = element("style");
			t = text("/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  --color-tint: #f8fbff;\n\n  --font-heading: \"Space Grotesk\", sans-serif;\n  --font-body: \"Open Sans\", sans-serif;\n\n  /* Colors */\n  --color-base: #183b56;\n  --color-brand: #1565d8;\n  --color-accent: #36b37e;\n  --color-accent-2: #0d2436;\n  --color-light: #fcfcfd;\n  --color-shade: #cbcace;\n  --color-inverted: white;\n  --color-tint: #e5eaf4;\n\n  /* Base values */\n  --color: var(--color-base);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #eee;\n  --background: white;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: var(--font-body);\n  color: var(--color-base);\n  line-height: 1.2;\n  font-size: 1.125rem;\n  background: var(--background);\n}\n\n.section.has-content {\n  display: flex;\n  justify-content: center;\n  padding: 5rem 2rem;\n}\n\n.section.has-content .content {\n    max-width: 800px;\n    width: 100%;\n  }\n\n.section-container {\n  max-width: 1250px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\n.heading-group {\n  display: grid;\n  gap: 1rem;\n  place-content: center;\n  text-align: center;\n}\n\n.heading-group .superhead {\n    font-family: var(--font-body);\n    color: var(--color-accent);\n    font-size: 0.875rem;\n    font-weight: 500;\n    letter-spacing: 1.5px;\n    text-transform: uppercase;\n  }\n\n.heading-group .subheading {\n    color: #4f6373;\n    line-height: 1.4;\n    max-width: 600px;\n    font-weight: 400;\n    max-width: 600px;\n    margin: 0 auto;\n  }\n\n.heading {\n  font-family: var(--font-heading);\n  font-size: 2rem;\n  line-height: 1.1;\n  font-weight: 500;\n  max-width: 600px;\n}\n\n.button {\n  color: var(--color-brand, white);\n  background: var(--color-inverted);\n  border: 2px solid var(--color-brand);\n  border-radius: 6px;\n  padding: 8px 20px;\n  transition: 0.1s background, 0.1s color;\n}\n\n.button:hover {\n    color: var(--color-inverted);\n    background: var(--color-brand);\n    border-color: var(--color-inverted);\n  }\n\n.button.inverted {\n    background: var(--color-white);\n    color: var(--color-brand);\n    border-color: #0d2436;\n  }\n\n.link {\n  font-size: 1.125rem;\n  font-weight: 400;\n  color: var(--color-brand);\n}\n\n.link .arrow {\n    transition: transform 0.1s;\n  }\n\n.link:hover .arrow {\n    transform: translateX(4px);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-95cp5n', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link0 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			link1 = claim_element(head_nodes, "LINK", { href: true, rel: true });
			link2 = claim_element(head_nodes, "LINK", { href: true, rel: true });

			link3 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  --color-tint: #f8fbff;\n\n  --font-heading: \"Space Grotesk\", sans-serif;\n  --font-body: \"Open Sans\", sans-serif;\n\n  /* Colors */\n  --color-base: #183b56;\n  --color-brand: #1565d8;\n  --color-accent: #36b37e;\n  --color-accent-2: #0d2436;\n  --color-light: #fcfcfd;\n  --color-shade: #cbcace;\n  --color-inverted: white;\n  --color-tint: #e5eaf4;\n\n  /* Base values */\n  --color: var(--color-base);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #eee;\n  --background: white;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: var(--font-body);\n  color: var(--color-base);\n  line-height: 1.2;\n  font-size: 1.125rem;\n  background: var(--background);\n}\n\n.section.has-content {\n  display: flex;\n  justify-content: center;\n  padding: 5rem 2rem;\n}\n\n.section.has-content .content {\n    max-width: 800px;\n    width: 100%;\n  }\n\n.section-container {\n  max-width: 1250px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\n.heading-group {\n  display: grid;\n  gap: 1rem;\n  place-content: center;\n  text-align: center;\n}\n\n.heading-group .superhead {\n    font-family: var(--font-body);\n    color: var(--color-accent);\n    font-size: 0.875rem;\n    font-weight: 500;\n    letter-spacing: 1.5px;\n    text-transform: uppercase;\n  }\n\n.heading-group .subheading {\n    color: #4f6373;\n    line-height: 1.4;\n    max-width: 600px;\n    font-weight: 400;\n    max-width: 600px;\n    margin: 0 auto;\n  }\n\n.heading {\n  font-family: var(--font-heading);\n  font-size: 2rem;\n  line-height: 1.1;\n  font-weight: 500;\n  max-width: 600px;\n}\n\n.button {\n  color: var(--color-brand, white);\n  background: var(--color-inverted);\n  border: 2px solid var(--color-brand);\n  border-radius: 6px;\n  padding: 8px 20px;\n  transition: 0.1s background, 0.1s color;\n}\n\n.button:hover {\n    color: var(--color-inverted);\n    background: var(--color-brand);\n    border-color: var(--color-inverted);\n  }\n\n.button.inverted {\n    background: var(--color-white);\n    color: var(--color-brand);\n    border-color: #0d2436;\n  }\n\n.link {\n  font-size: 1.125rem;\n  font-weight: 400;\n  color: var(--color-brand);\n}\n\n.link .arrow {\n    transition: transform 0.1s;\n  }\n\n.link:hover .arrow {\n    transform: translateX(4px);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link0, "rel", "preconnect");
			attr(link0, "href", "https://fonts.bunny.net");
			attr(link1, "href", "https://fonts.bunny.net/css?family=fredoka:300,400,500,600,700|space-grotesk:300,400,500,600,700");
			attr(link1, "rel", "stylesheet");
			attr(link2, "href", "https://fonts.bunny.net/css?family=fredoka:300,400,500,600,700|open-sans:300,300i,400,400i,500,500i,600,600i,700,700i,800,800i|space-grotesk:300,400,500,600,700");
			attr(link2, "rel", "stylesheet");
			attr(link3, "rel", "icon");
			attr(link3, "type", "image/png");
			attr(link3, "sizes", "32x32");
			attr(link3, "href", link3_href_value = /*favicon*/ ctx[0].url);
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, link2);
			append_hydration(document.head, link3);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 1 && link3_href_value !== (link3_href_value = /*favicon*/ ctx[0].url)) {
				attr(link3, "href", link3_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link0);
			detach(link1);
			detach(link2);
			detach(link3);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { favicon: 0 });
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	child_ctx[10] = i;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	child_ctx[10] = i;
	return child_ctx;
}

function get_each_context_3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

// (131:8) {:else}
function create_else_block_1(ctx) {
	let span;
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			span = element("span");
			t = text(t_value);
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			var span_nodes = children(span);
			t = claim_text(span_nodes, t_value);
			span_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (129:8) {#if logo.image.url}
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (136:8) {#each site_nav as { link }}
function create_each_block_3(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "nav-item svelte-6vjs4t");
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (139:8) {#each cta as { link }
function create_each_block_2(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "button svelte-6vjs4t");
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*cta*/ 4 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*cta*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (150:4) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t0;
	let t1;
	let hr;
	let t2;
	let t3;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].image.url) return create_if_block_1$1;
		return create_else_block$1;
	}

	let current_block_type = select_block_type_1(ctx);
	let if_block = current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	let each_value = /*cta*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { icon: "ph:x-duotone" } });

	return {
		c() {
			nav = element("nav");
			if_block.c();
			t0 = space();

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t1 = space();
			hr = element("hr");
			t2 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t3 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);
			if_block.l(nav_nodes);
			t0 = claim_space(nav_nodes);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);
			hr = claim_element(nav_nodes, "HR", { class: true });
			t2 = claim_space(nav_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t3 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(hr, "class", "svelte-6vjs4t");
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-6vjs4t");
			attr(nav, "id", "mobile-nav");
			attr(nav, "class", "svelte-6vjs4t");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);
			if_block.m(nav, null);
			append_hydration(nav, t0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);
			append_hydration(nav, hr);
			append_hydration(nav, t2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t3);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type_1(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(nav, t0);
				}
			}

			if (dirty & /*site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(nav, t1);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty & /*cta*/ 4) {
				each_value = /*cta*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t3);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			if_block.d();
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (154:8) {:else}
function create_else_block$1(ctx) {
	let span;
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			span = element("span");
			t = text(t_value);
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			var span_nodes = children(span);
			t = claim_text(span_nodes, t_value);
			span_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (152:8) {#if logo.image.url}
function create_if_block_1$1(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (157:8) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(a, "class", "svelte-6vjs4t");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (161:8) {#each cta as { link }
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(a, "class", "button svelte-6vjs4t");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*cta*/ 4 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*cta*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div2;
	let header;
	let div1;
	let div0;
	let a;
	let style___size = `${/*logo*/ ctx[0].size}rem`;
	let t0;
	let nav;
	let t1;
	let t2;
	let button;
	let icon;
	let t3;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].image.url) return create_if_block_2;
		return create_else_block_1;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type(ctx);
	let each_value_3 = /*site_nav*/ ctx[1];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_3.length; i += 1) {
		each_blocks_1[i] = create_each_block_3(get_each_context_3(ctx, each_value_3, i));
	}

	let each_value_2 = /*cta*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks[i] = create_each_block_2(get_each_context_2(ctx, each_value_2, i));
	}

	icon = new Component$1({ props: { icon: "ic:round-menu" } });
	let if_block1 = /*mobileNavOpen*/ ctx[3] && create_if_block$1(ctx);

	return {
		c() {
			div2 = element("div");
			header = element("header");
			div1 = element("div");
			div0 = element("div");
			a = element("a");
			if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t1 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t3 = space();
			if (if_block1) if_block1.c();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a = claim_element(div0_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			if_block0.l(a_nodes);
			a_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t2 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block1) if_block1.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", "/");
			attr(a, "class", "logo svelte-6vjs4t");
			set_style(a, "--size", style___size);
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(button, "class", "svelte-6vjs4t");
			attr(nav, "class", "svelte-6vjs4t");
			attr(div0, "class", "desktop-nav svelte-6vjs4t");
			attr(div1, "class", "section-container svelte-6vjs4t");
			attr(header, "class", "svelte-6vjs4t");
			attr(div2, "class", "section");
			attr(div2, "id", "section-c958ca7d");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, header);
			append_hydration(header, div1);
			append_hydration(div1, div0);
			append_hydration(div0, a);
			if_block0.m(a, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t2);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			append_hydration(div1, t3);
			if (if_block1) if_block1.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[5]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if_block0.d(1);
				if_block0 = current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a, null);
				}
			}

			if (dirty & /*logo*/ 1 && style___size !== (style___size = `${/*logo*/ ctx[0].size}rem`)) {
				set_style(a, "--size", style___size);
			}

			if (dirty & /*site_nav*/ 2) {
				each_value_3 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_3.length; i += 1) {
					const child_ctx = get_each_context_3(ctx, each_value_3, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_3(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(nav, t1);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_3.length;
			}

			if (dirty & /*cta*/ 4) {
				each_value_2 = /*cta*/ ctx[2];
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2(ctx, each_value_2, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t2);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_2.length;
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block1) {
					if_block1.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block1, 1);
					}
				} else {
					if_block1 = create_if_block$1(ctx);
					if_block1.c();
					transition_in(if_block1, 1);
					if_block1.m(div1, null);
				}
			} else if (if_block1) {
				group_outros();

				transition_out(if_block1, 1, 1, () => {
					if_block1 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block1);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block1);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			if_block0.d();
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (if_block1) if_block1.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { cta } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(3, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(3, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('cta' in $$props) $$invalidate(2, cta = $$props.cta);
	};

	return [logo, site_nav, cta, mobileNavOpen, favicon, click_handler, click_handler_1];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$2, create_fragment$2, safe_not_equal, { favicon: 4, logo: 0, site_nav: 1, cta: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function create_if_block$2(ctx) {
	let a;
	let t_value = /*link*/ ctx[2].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[2].url);
			attr(a, "class", "button svelte-8pf9op");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*link*/ 4 && t_value !== (t_value = /*link*/ ctx[2].label + "")) set_data(t, t_value);

			if (dirty & /*link*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$3(ctx) {
	let div3;
	let section;
	let div2;
	let div1;
	let h1;
	let t0;
	let t1;
	let div0;
	let t2;
	let t3;
	let t4;
	let figure;
	let img;
	let img_src_value;
	let img_alt_value;
	let t5;
	let svg;
	let path0;
	let path1;
	let path2;
	let if_block = /*link*/ ctx[2].label && create_if_block$2(ctx);

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			div1 = element("div");
			h1 = element("h1");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			if (if_block) if_block.c();
			t4 = space();
			figure = element("figure");
			img = element("img");
			t5 = space();
			svg = svg_element("svg");
			path0 = svg_element("path");
			path1 = svg_element("path");
			path2 = svg_element("path");
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h1 = claim_element(div1_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, /*heading*/ ctx[0]);
			h1_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t2 = claim_text(div0_nodes, /*subheading*/ ctx[1]);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			div1_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			figure = claim_element(div2_nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);
			img = claim_element(figure_nodes, "IMG", { src: true, alt: true, class: true });
			t5 = claim_space(figure_nodes);

			svg = claim_svg_element(figure_nodes, "svg", {
				width: true,
				height: true,
				viewBox: true,
				fill: true,
				xmlns: true,
				class: true
			});

			var svg_nodes = children(svg);

			path0 = claim_svg_element(svg_nodes, "path", {
				opacity: true,
				"fill-rule": true,
				"clip-rule": true,
				d: true,
				fill: true
			});

			children(path0).forEach(detach);

			path1 = claim_svg_element(svg_nodes, "path", {
				opacity: true,
				"fill-rule": true,
				"clip-rule": true,
				d: true,
				fill: true
			});

			children(path1).forEach(detach);

			path2 = claim_svg_element(svg_nodes, "path", {
				opacity: true,
				"fill-rule": true,
				"clip-rule": true,
				d: true,
				fill: true
			});

			children(path2).forEach(detach);
			svg_nodes.forEach(detach);
			figure_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "headline svelte-8pf9op");
			attr(div0, "class", "subheading svelte-8pf9op");
			attr(div1, "class", "body svelte-8pf9op");
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[3].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[3].alt);
			attr(img, "class", "svelte-8pf9op");
			attr(path0, "opacity", "0.05");
			attr(path0, "fill-rule", "evenodd");
			attr(path0, "clip-rule", "evenodd");
			attr(path0, "d", "M250.362 34.7756C139.816 89.1131 67.3668 143.319 26.8947 207.101C4.61533 242.212 -2.94332 266.681 0.997026 292.673C4.60124 316.447 16.5768 340.207 47.4378 388.613C60.4002 408.945 60.0371 441.564 49.6915 487.99C47.2186 499.088 44.2927 510.565 40.3577 524.955C41.2971 521.519 31.5889 556.493 29.4742 564.688C26.0093 578.117 24.0811 587.645 23.5326 594.881C20.1621 639.352 54.9001 672.353 110.767 684.383C164.801 696.018 227.511 685.427 270.671 655.274C276.453 651.234 291.181 640.89 299.95 634.731C303.38 632.322 305.898 630.554 306.613 630.053C319.856 620.775 329.589 614.052 338.766 607.882C361.325 592.713 379.332 581.766 396.694 572.934C446.494 547.603 494.541 538.614 565.78 542.901C598.07 544.844 628.45 533.685 653.596 512.012C676.988 491.852 694.617 463.505 703.223 432.744C712.019 401.304 710.848 369.433 699.177 342.706C686.32 313.263 661.427 291.233 625.376 279.556C586.268 266.888 569.43 251.107 569.005 230.46C568.824 221.657 571.541 211.918 577.065 200.127C581.082 191.553 581.928 190.056 595.678 166.497C610.379 141.308 617.427 126.392 620.883 109.77C625.398 88.0522 621.377 68.3247 606.92 49.4498C584.428 20.0847 524.241 2.47769 448.511 0.238031C375.056 -1.93434 299.024 10.8562 250.362 34.7756ZM3.58288 292.383C-0.275778 266.93 7.14569 242.905 29.1841 208.174C69.3833 144.822 141.492 90.8709 251.657 36.7206C299.855 13.0296 375.416 0.318108 448.422 2.4772C523.388 4.69424 582.842 22.087 604.745 50.6819C618.819 69.0565 622.721 88.2016 618.318 109.375C614.92 125.722 607.943 140.487 593.35 165.493C579.553 189.133 578.705 190.631 574.649 199.29C569.005 211.335 566.212 221.348 566.4 230.5C566.847 252.198 584.446 268.691 624.459 281.652C659.794 293.098 684.141 314.644 696.738 343.493C708.216 369.777 709.371 401.195 700.69 432.22C692.193 462.594 674.793 490.572 651.753 510.429C627.112 531.665 597.453 542.56 565.964 540.666C494.212 536.348 445.638 545.435 395.368 571.006C377.895 579.894 359.802 590.894 337.162 606.117C327.969 612.298 318.223 619.03 304.968 628.316C304.254 628.816 301.742 630.58 298.321 632.983C289.554 639.14 274.812 649.494 269.029 653.535C226.525 683.229 164.661 693.678 111.402 682.209C56.6608 670.422 22.8546 638.306 26.1348 595.026C26.6724 587.934 28.5821 578.498 32.0201 565.173C34.1294 556.999 43.8307 522.05 42.8962 525.467C46.8388 511.05 49.7718 499.545 52.2527 488.412C62.7082 441.493 63.0757 408.477 49.7247 387.536C19.0189 339.374 7.13099 315.787 3.58288 292.383Z");
			attr(path0, "fill", "white");
			attr(path1, "opacity", "0.15");
			attr(path1, "fill-rule", "evenodd");
			attr(path1, "clip-rule", "evenodd");
			attr(path1, "d", "M397.33 27.2727C343.179 32.0545 282.134 51.1101 228.45 78.1813C225.981 79.4262 219.504 82.6078 211.35 86.6135C192.691 95.7792 165.248 109.259 156.946 113.724C131.078 127.633 113.909 140.497 97.0005 159.654C80.3265 178.545 63.6534 204.133 42.8539 242.71C34.4888 263.275 33.3473 281.11 38.2328 298.299C41.9884 311.513 47.7933 321.819 60.868 340.936C61.2972 341.563 61.7281 342.193 62.5888 343.449C77.6086 365.384 83.6274 376.237 87.2636 391.215C92.0442 410.908 89.2721 431.928 77.2375 456.81C51.1289 514.119 42.7176 560.754 50.4159 596.281C57.2991 628.047 77.0019 650.185 106.511 661.927C160.111 683.254 241.068 666.921 291.203 626.602C297.109 621.853 314.582 607.723 318.819 604.297L319.749 603.545C330.387 594.96 338.104 588.805 345.421 583.099C363.536 568.974 377.991 558.618 391.925 550.002C436.098 522.686 478.642 511.444 544.34 511.444C600.73 511.444 646.661 465.922 658.264 406.507C663.796 378.183 660.462 350.008 648.191 326.946C634.67 301.535 611.009 283.335 578.204 274.908C542.857 265.827 526.843 252.858 524.881 234.783C524.042 227.061 525.69 218.356 529.658 207.72C532.571 199.914 533.825 197.231 543.585 177.15C556.994 149.564 562.475 134.02 562.697 116.633C562.902 100.517 557.486 85.8734 545.376 72.243C512.97 35.769 461.447 21.6109 397.33 27.2727ZM212.567 88.5959C220.759 84.5714 227.277 81.3696 229.768 80.1136C283.151 53.1947 343.848 34.2475 397.596 29.5013C460.886 23.9125 511.517 37.8251 543.304 73.6028C555.054 86.8275 560.289 100.983 560.09 116.608C559.873 133.615 554.463 148.958 541.18 176.286C531.38 196.447 530.122 199.14 527.176 207.035C523.109 217.934 521.409 226.92 522.285 234.991C524.36 254.109 541.189 267.737 577.457 277.054C609.53 285.293 632.606 303.044 645.82 327.878C657.862 350.509 661.143 378.233 655.693 406.136C644.279 464.582 599.258 509.204 544.34 509.204C478.107 509.204 435.029 520.586 390.402 548.183C376.377 556.856 361.851 567.263 343.669 581.44C336.34 587.155 328.612 593.319 317.964 601.912L317.073 602.632C312.904 606.003 295.343 620.204 289.422 624.966C240.015 664.699 160.169 680.808 107.605 659.893C78.8689 648.459 59.7074 626.929 52.9774 595.871C45.3799 560.809 53.7184 514.577 79.6535 457.649C91.8734 432.384 94.7058 410.907 89.8143 390.757C86.102 375.465 79.9933 364.451 64.8342 342.313C63.9734 341.056 63.5429 340.427 63.114 339.8C50.1623 320.863 44.4414 310.706 40.7639 297.767C35.9995 281.003 37.1128 263.61 45.2658 243.551C65.9455 205.208 82.5351 179.749 99.0761 161.008C115.78 142.084 132.712 129.396 158.327 115.623C166.577 111.187 193.913 97.7591 212.567 88.5959Z");
			attr(path1, "fill", "white");
			attr(path2, "opacity", "0.2");
			attr(path2, "fill-rule", "evenodd");
			attr(path2, "clip-rule", "evenodd");
			attr(path2, "d", "M393.65 53.3234C356.923 60.458 317.486 75.5292 246.32 107.518C200.301 128.204 185.067 135.564 170.938 144.573C157.451 153.174 148.276 161.866 139.021 174.653C133.336 182.507 127.789 191.512 118.361 207.865C117.548 209.275 115.274 213.239 112.783 217.58C109.803 222.774 106.513 228.509 105.045 231.056C99.153 241.276 93.8182 250.4 88.1163 259.962C74.6004 282.628 69.9213 297.456 72.5119 307.421C74.6266 315.557 80.2875 319.73 93.5713 325.271C94.1179 325.499 95.5342 326.084 96.6564 326.547C97.3304 326.825 97.8983 327.06 98.1079 327.147C99.9117 327.896 101.335 328.502 102.708 329.114C117.63 335.754 125.95 343.298 129.949 357.07C135.142 374.951 131.492 401.884 117.069 440.958C115.82 444.341 114.547 447.769 112.872 452.264C113.073 451.724 109.685 460.813 108.769 463.276C105.503 472.056 103.194 478.347 101.032 484.399C95.529 499.805 91.6296 511.939 88.78 522.912C81.9545 549.193 81.3792 568.6 88.0542 584.062C104.844 622.952 140.549 638.02 187.399 632.019C225.701 627.113 269.161 607.709 298.006 584.49C299.122 583.592 301.968 581.287 305.333 578.561C311.157 573.844 318.535 567.868 321.192 565.745C329.222 559.328 335.462 554.56 341.49 550.301C362.227 535.651 381.62 526.536 410.239 518.761C418.131 516.616 425.218 514.298 431.856 511.743C437.879 509.426 443.267 507.032 449.426 504.029C449.733 503.879 450.715 503.391 452.037 502.734C455.555 500.986 461.485 498.038 463.555 497.064C478.371 490.093 490.675 487.259 511.496 487.259C559.201 487.259 598.033 448.734 607.84 398.469C612.515 374.51 609.697 350.675 599.324 331.161C587.889 309.65 567.875 294.241 540.133 287.107C510.429 279.469 495.587 264.944 491.837 243.158C488.939 226.326 491.787 209.512 501.245 174.95C501.445 174.221 501.634 173.53 501.944 172.4C509.564 144.612 512.193 132.893 512.954 119.095C513.967 100.722 509.759 86.6352 498.848 76.0643C473.083 51.1011 439.07 44.5001 393.65 53.3234ZM172.489 146.372C186.462 137.462 201.649 130.125 247.526 109.504C318.49 77.6051 357.792 62.5856 394.223 55.5085C438.788 46.8512 471.83 53.2638 496.897 77.551C507.292 87.6221 511.333 101.148 510.349 118.988C509.598 132.598 506.987 144.24 499.406 171.886C499.096 173.016 498.906 173.707 498.707 174.437C489.169 209.286 486.293 226.269 489.256 243.486C493.156 266.139 508.718 281.368 539.384 289.253C566.394 296.198 585.823 311.158 596.951 332.092C607.096 351.176 609.861 374.56 605.268 398.098C595.65 447.395 557.726 485.018 511.494 485.018C490.225 485.018 477.493 487.951 462.302 495.098C460.197 496.089 454.202 499.068 450.692 500.813C449.394 501.459 448.435 501.935 448.139 502.08C442.046 505.05 436.729 507.412 430.789 509.698C424.243 512.217 417.249 514.505 409.452 516.624C380.512 524.486 360.825 533.739 339.833 548.57C333.758 552.862 327.481 557.658 319.415 564.104C316.751 566.233 309.36 572.22 303.533 576.938C300.174 579.659 297.335 581.959 296.223 582.854C267.747 605.776 224.763 624.967 187.013 629.803C141.308 635.657 106.825 621.105 90.4958 583.282C84.0323 568.31 84.596 549.297 91.3217 523.399C94.1541 512.494 98.0368 500.412 103.522 485.057C105.68 479.015 107.986 472.731 111.249 463.958C112.165 461.496 115.553 452.408 115.353 452.947C117.028 448.45 118.301 445.021 119.551 441.635C134.107 402.202 137.809 374.889 132.476 356.527C128.271 342.047 119.434 334.034 103.905 327.123C102.506 326.501 101.063 325.886 99.2396 325.129C99.0265 325.04 98.4513 324.803 97.7711 324.522C96.6513 324.06 95.2472 323.48 94.7071 323.255C82.083 317.989 76.9426 314.199 75.0535 306.932C72.6313 297.614 77.1733 283.221 90.4337 260.984C96.1415 251.412 101.482 242.279 107.378 232.05C108.848 229.5 112.142 223.759 115.123 218.562C117.612 214.225 119.883 210.267 120.694 208.86C130.087 192.569 135.604 183.611 141.232 175.836C150.318 163.284 159.27 154.801 172.489 146.372Z");
			attr(path2, "fill", "white");
			attr(svg, "width", "709");
			attr(svg, "height", "689");
			attr(svg, "viewBox", "0 0 709 689");
			attr(svg, "fill", "none");
			attr(svg, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg, "class", "svelte-8pf9op");
			attr(figure, "class", "svelte-8pf9op");
			attr(div2, "class", "section-container svelte-8pf9op");
			attr(section, "class", "svelte-8pf9op");
			toggle_class(section, "image-left", /*variation*/ ctx[4] === "image_left");
			attr(div3, "class", "section");
			attr(div3, "id", "section-6af3f1f6");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, div1);
			append_hydration(div1, h1);
			append_hydration(h1, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);
			append_hydration(div0, t2);
			append_hydration(div1, t3);
			if (if_block) if_block.m(div1, null);
			append_hydration(div2, t4);
			append_hydration(div2, figure);
			append_hydration(figure, img);
			append_hydration(figure, t5);
			append_hydration(figure, svg);
			append_hydration(svg, path0);
			append_hydration(svg, path1);
			append_hydration(svg, path2);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (/*link*/ ctx[2].label) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$2(ctx);
					if_block.c();
					if_block.m(div1, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*image*/ 8 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[3].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 8 && img_alt_value !== (img_alt_value = /*image*/ ctx[3].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*variation*/ 16) {
				toggle_class(section, "image-left", /*variation*/ ctx[4] === "image_left");
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
			if (if_block) if_block.d();
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { link } = $$props;
	let { image } = $$props;
	let { variation } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('link' in $$props) $$invalidate(2, link = $$props.link);
		if ('image' in $$props) $$invalidate(3, image = $$props.image);
		if ('variation' in $$props) $$invalidate(4, variation = $$props.variation);
	};

	return [heading, subheading, link, image, variation, favicon];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 5,
			heading: 0,
			subheading: 1,
			link: 2,
			image: 3,
			variation: 4
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i];
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].icon;
	child_ctx[10] = list[i].label;
	return child_ctx;
}

// (101:4) {#each icon_list as { icon, label }}
function create_each_block_1$1(ctx) {
	let li;
	let span0;
	let icon;
	let t0;
	let span1;
	let t1_value = /*label*/ ctx[10] + "";
	let t1;
	let t2;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[9] } });

	return {
		c() {
			li = element("li");
			span0 = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			span1 = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			span0 = claim_element(li_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			claim_component(icon.$$.fragment, span0_nodes);
			span0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			span1 = claim_element(li_nodes, "SPAN", {});
			var span1_nodes = children(span1);
			t1 = claim_text(span1_nodes, t1_value);
			span1_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "icon svelte-udcuzo");
			attr(li, "class", "svelte-udcuzo");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, span0);
			mount_component(icon, span0, null);
			append_hydration(li, t0);
			append_hydration(li, span1);
			append_hydration(span1, t1);
			append_hydration(li, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*icon_list*/ 8) icon_changes.icon = /*icon*/ ctx[9];
			icon.$set(icon_changes);
			if ((!current || dirty & /*icon_list*/ 8) && t1_value !== (t1_value = /*label*/ ctx[10] + "")) set_data(t1, t1_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

// (111:4) {#each cards as card}
function create_each_block$1(ctx) {
	let li;
	let div0;
	let icon0;
	let t0;
	let div3;
	let h3;
	let t1_value = /*card*/ ctx[6].title + "";
	let t1;
	let t2;
	let div1;
	let raw_value = /*card*/ ctx[6].content.html + "";
	let t3;
	let a;
	let span;
	let t4_value = /*card*/ ctx[6].link.label + "";
	let t4;
	let t5;
	let div2;
	let icon1;
	let a_href_value;
	let t6;
	let current;
	icon0 = new Component$1({ props: { icon: /*card*/ ctx[6].icon } });

	icon1 = new Component$1({
			props: { icon: "akar-icons:arrow-right" }
		});

	return {
		c() {
			li = element("li");
			div0 = element("div");
			create_component(icon0.$$.fragment);
			t0 = space();
			div3 = element("div");
			h3 = element("h3");
			t1 = text(t1_value);
			t2 = space();
			div1 = element("div");
			t3 = space();
			a = element("a");
			span = element("span");
			t4 = text(t4_value);
			t5 = space();
			div2 = element("div");
			create_component(icon1.$$.fragment);
			t6 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			div0 = claim_element(li_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			claim_component(icon0.$$.fragment, div0_nodes);
			div0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			div3 = claim_element(li_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			h3 = claim_element(div3_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t1 = claim_text(h3_nodes, t1_value);
			h3_nodes.forEach(detach);
			t2 = claim_space(div3_nodes);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div1_nodes.forEach(detach);
			t3 = claim_space(div3_nodes);
			a = claim_element(div3_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			span = claim_element(a_nodes, "SPAN", {});
			var span_nodes = children(span);
			t4 = claim_text(span_nodes, t4_value);
			span_nodes.forEach(detach);
			t5 = claim_space(a_nodes);
			div2 = claim_element(a_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			claim_component(icon1.$$.fragment, div2_nodes);
			div2_nodes.forEach(detach);
			a_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t6 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "icon svelte-udcuzo");
			attr(h3, "class", "title svelte-udcuzo");
			attr(div1, "class", "content svelte-udcuzo");
			attr(div2, "class", "arrow");
			attr(a, "href", a_href_value = /*card*/ ctx[6].link.url);
			attr(a, "class", "link svelte-udcuzo");
			attr(div3, "class", "body svelte-udcuzo");
			attr(li, "class", "svelte-udcuzo");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, div0);
			mount_component(icon0, div0, null);
			append_hydration(li, t0);
			append_hydration(li, div3);
			append_hydration(div3, h3);
			append_hydration(h3, t1);
			append_hydration(div3, t2);
			append_hydration(div3, div1);
			div1.innerHTML = raw_value;
			append_hydration(div3, t3);
			append_hydration(div3, a);
			append_hydration(a, span);
			append_hydration(span, t4);
			append_hydration(a, t5);
			append_hydration(a, div2);
			mount_component(icon1, div2, null);
			append_hydration(li, t6);
			current = true;
		},
		p(ctx, dirty) {
			const icon0_changes = {};
			if (dirty & /*cards*/ 16) icon0_changes.icon = /*card*/ ctx[6].icon;
			icon0.$set(icon0_changes);
			if ((!current || dirty & /*cards*/ 16) && t1_value !== (t1_value = /*card*/ ctx[6].title + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*cards*/ 16) && raw_value !== (raw_value = /*card*/ ctx[6].content.html + "")) div1.innerHTML = raw_value;			if ((!current || dirty & /*cards*/ 16) && t4_value !== (t4_value = /*card*/ ctx[6].link.label + "")) set_data(t4, t4_value);

			if (!current || dirty & /*cards*/ 16 && a_href_value !== (a_href_value = /*card*/ ctx[6].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon0.$$.fragment, local);
			transition_in(icon1.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon0.$$.fragment, local);
			transition_out(icon1.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon0);
			destroy_component(icon1);
		}
	};
}

function create_fragment$4(ctx) {
	let div2;
	let section;
	let header;
	let div0;
	let t0;
	let t1;
	let h2;
	let t2;
	let div1;
	let t3;
	let t4;
	let ul0;
	let t5;
	let ul1;
	let current;
	let each_value_1 = /*icon_list*/ ctx[3];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks_1[i], 1, 1, () => {
		each_blocks_1[i] = null;
	});

	let each_value = /*cards*/ ctx[4];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	const out_1 = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div2 = element("div");
			section = element("section");
			header = element("header");
			div0 = element("div");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h2 = element("h2");
			t2 = space();
			div1 = element("div");
			t3 = text(/*subhead*/ ctx[2]);
			t4 = space();
			ul0 = element("ul");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t5 = space();
			ul1 = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			header = claim_element(section_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t0 = claim_text(div0_nodes, /*superhead*/ ctx[0]);
			div0_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			h2 = claim_element(header_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			h2_nodes.forEach(detach);
			t2 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			t3 = claim_text(div1_nodes, /*subhead*/ ctx[2]);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t4 = claim_space(section_nodes);
			ul0 = claim_element(section_nodes, "UL", { class: true });
			var ul0_nodes = children(ul0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(ul0_nodes);
			}

			ul0_nodes.forEach(detach);
			t5 = claim_space(section_nodes);
			ul1 = claim_element(section_nodes, "UL", { class: true });
			var ul1_nodes = children(ul1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul1_nodes);
			}

			ul1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "superhead");
			attr(h2, "class", "heading svelte-udcuzo");
			attr(div1, "class", "subheading");
			attr(header, "class", "heading-group svelte-udcuzo");
			attr(ul0, "class", "icon-list svelte-udcuzo");
			attr(ul1, "class", "cards svelte-udcuzo");
			attr(section, "class", "section-container svelte-udcuzo");
			attr(div2, "class", "section");
			attr(div2, "id", "section-d633345a");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, section);
			append_hydration(section, header);
			append_hydration(header, div0);
			append_hydration(div0, t0);
			append_hydration(header, t1);
			append_hydration(header, h2);
			h2.innerHTML = /*heading*/ ctx[1];
			append_hydration(header, t2);
			append_hydration(header, div1);
			append_hydration(div1, t3);
			append_hydration(section, t4);
			append_hydration(section, ul0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(ul0, null);
				}
			}

			append_hydration(section, t5);
			append_hydration(section, ul1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul1, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*superhead*/ 1) set_data(t0, /*superhead*/ ctx[0]);
			if (!current || dirty & /*heading*/ 2) h2.innerHTML = /*heading*/ ctx[1];			if (!current || dirty & /*subhead*/ 4) set_data(t3, /*subhead*/ ctx[2]);

			if (dirty & /*icon_list*/ 8) {
				each_value_1 = /*icon_list*/ ctx[3];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
						transition_in(each_blocks_1[i], 1);
					} else {
						each_blocks_1[i] = create_each_block_1$1(child_ctx);
						each_blocks_1[i].c();
						transition_in(each_blocks_1[i], 1);
						each_blocks_1[i].m(ul0, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks_1.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (dirty & /*cards*/ 16) {
				each_value = /*cards*/ ctx[4];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul1, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out_1(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks_1[i]);
			}

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks_1 = each_blocks_1.filter(Boolean);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				transition_out(each_blocks_1[i]);
			}

			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { superhead } = $$props;
	let { heading } = $$props;
	let { subhead } = $$props;
	let { icon_list } = $$props;
	let { cards } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('subhead' in $$props) $$invalidate(2, subhead = $$props.subhead);
		if ('icon_list' in $$props) $$invalidate(3, icon_list = $$props.icon_list);
		if ('cards' in $$props) $$invalidate(4, cards = $$props.cards);
	};

	return [superhead, heading, subhead, icon_list, cards, favicon];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			favicon: 5,
			superhead: 0,
			heading: 1,
			subhead: 2,
			icon_list: 3,
			cards: 4
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i].image;
	return child_ctx;
}

// (67:6) {#each logos as {image}}
function create_each_block$2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[5].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[5].alt);
			attr(img, "class", "svelte-n8wxh7");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logos*/ 4 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[5].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logos*/ 4 && img_alt_value !== (img_alt_value = /*image*/ ctx[5].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

function create_fragment$5(ctx) {
	let div2;
	let svg;
	let path;
	let t0;
	let section;
	let div1;
	let header;
	let span;
	let t1;
	let t2;
	let h2;
	let t3;
	let t4;
	let div0;
	let div0_class_value;
	let each_value = /*logos*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			svg = svg_element("svg");
			path = svg_element("path");
			t0 = space();
			section = element("section");
			div1 = element("div");
			header = element("header");
			span = element("span");
			t1 = text(/*superhead*/ ctx[0]);
			t2 = space();
			h2 = element("h2");
			t3 = text(/*heading*/ ctx[1]);
			t4 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			svg = claim_svg_element(div2_nodes, "svg", { viewBox: true, fill: true, xmlns: true });
			var svg_nodes = children(svg);

			path = claim_svg_element(svg_nodes, "path", {
				"fill-rule": true,
				"clip-rule": true,
				d: true,
				fill: true
			});

			children(path).forEach(detach);
			svg_nodes.forEach(detach);
			t0 = claim_space(div2_nodes);
			section = claim_element(div2_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			header = claim_element(div1_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			span = claim_element(header_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, /*superhead*/ ctx[0]);
			span_nodes.forEach(detach);
			t2 = claim_space(header_nodes);
			h2 = claim_element(header_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t3 = claim_text(h2_nodes, /*heading*/ ctx[1]);
			h2_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(path, "fill-rule", "evenodd");
			attr(path, "clip-rule", "evenodd");
			attr(path, "d", "M1440 175H0V0C240 53.3333 480 80 720 80C960 80 1200 53.3333 1440 0V175Z");
			attr(path, "fill", "var(--color-tint)");
			attr(svg, "viewBox", "0 0 1440 175");
			attr(svg, "fill", "none");
			attr(svg, "xmlns", "http://www.w3.org/2000/svg");
			attr(span, "class", "superhead");
			attr(h2, "class", "heading");
			attr(header, "class", "heading-group svelte-n8wxh7");
			attr(div0, "class", div0_class_value = "logos " + /*logo_size*/ ctx[3] + " svelte-n8wxh7");
			attr(div1, "class", "section-container svelte-n8wxh7");
			attr(section, "class", "svelte-n8wxh7");
			attr(div2, "class", "section");
			attr(div2, "id", "section-7e11ffdb");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, svg);
			append_hydration(svg, path);
			append_hydration(div2, t0);
			append_hydration(div2, section);
			append_hydration(section, div1);
			append_hydration(div1, header);
			append_hydration(header, span);
			append_hydration(span, t1);
			append_hydration(header, t2);
			append_hydration(header, h2);
			append_hydration(h2, t3);
			append_hydration(div1, t4);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*superhead*/ 1) set_data(t1, /*superhead*/ ctx[0]);
			if (dirty & /*heading*/ 2) set_data(t3, /*heading*/ ctx[1]);

			if (dirty & /*logos*/ 4) {
				each_value = /*logos*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*logo_size*/ 8 && div0_class_value !== (div0_class_value = "logos " + /*logo_size*/ ctx[3] + " svelte-n8wxh7")) {
				attr(div0, "class", div0_class_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { superhead } = $$props;
	let { heading } = $$props;
	let { logos } = $$props;
	let { logo_size } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('logos' in $$props) $$invalidate(2, logos = $$props.logos);
		if ('logo_size' in $$props) $$invalidate(3, logo_size = $$props.logo_size);
	};

	return [superhead, heading, logos, logo_size, favicon];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			favicon: 4,
			superhead: 0,
			heading: 1,
			logos: 2,
			logo_size: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$6(ctx) {
	let div1;
	let div0;
	let hr;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			hr = element("hr");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			hr = claim_element(div0_nodes, "HR", {});
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container svelte-1nxn5fd");
			attr(div1, "class", "section");
			attr(div1, "id", "section-8a8d6d40");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, hr);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$6, create_fragment$6, safe_not_equal, { favicon: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i];
	return child_ctx;
}

// (89:8) {#if teaser.image.url}
function create_if_block_1$2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*teaser*/ ctx[5].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*teaser*/ ctx[5].image.alt);
			attr(img, "class", "svelte-3pbbnz");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*teasers*/ 8 && !src_url_equal(img.src, img_src_value = /*teaser*/ ctx[5].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*teasers*/ 8 && img_alt_value !== (img_alt_value = /*teaser*/ ctx[5].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (95:10) {#if teaser.link.url}
function create_if_block$3(ctx) {
	let a;
	let t0_value = /*teaser*/ ctx[5].link.label + "";
	let t0;
	let t1;
	let div;
	let icon;
	let a_href_value;
	let current;

	icon = new Component$1({
			props: { icon: "akar-icons:arrow-right" }
		});

	return {
		c() {
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			div = element("div");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			t1 = claim_space(a_nodes);
			div = claim_element(a_nodes, "DIV", { class: true });
			var div_nodes = children(div);
			claim_component(icon.$$.fragment, div_nodes);
			div_nodes.forEach(detach);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "arrow");
			attr(a, "class", "link svelte-3pbbnz");
			attr(a, "href", a_href_value = /*teaser*/ ctx[5].link.url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t0);
			append_hydration(a, t1);
			append_hydration(a, div);
			mount_component(icon, div, null);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*teasers*/ 8) && t0_value !== (t0_value = /*teaser*/ ctx[5].link.label + "")) set_data(t0, t0_value);

			if (!current || dirty & /*teasers*/ 8 && a_href_value !== (a_href_value = /*teaser*/ ctx[5].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

// (87:4) {#each teasers as teaser}
function create_each_block$3(ctx) {
	let div2;
	let t0;
	let div1;
	let h2;
	let t1_value = /*teaser*/ ctx[5].title + "";
	let t1;
	let t2;
	let div0;
	let raw_value = /*teaser*/ ctx[5].content.html + "";
	let t3;
	let t4;
	let current;
	let if_block0 = /*teaser*/ ctx[5].image.url && create_if_block_1$2(ctx);
	let if_block1 = /*teaser*/ ctx[5].link.url && create_if_block$3(ctx);

	return {
		c() {
			div2 = element("div");
			if (if_block0) if_block0.c();
			t0 = space();
			div1 = element("div");
			h2 = element("h2");
			t1 = text(t1_value);
			t2 = space();
			div0 = element("div");
			t3 = space();
			if (if_block1) if_block1.c();
			t4 = space();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			if (if_block0) if_block0.l(div2_nodes);
			t0 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t1 = claim_text(h2_nodes, t1_value);
			h2_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block1) if_block1.l(div1_nodes);
			div1_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "title svelte-3pbbnz");
			attr(div0, "class", "content");
			attr(div1, "class", "body svelte-3pbbnz");
			attr(div2, "class", "teaser svelte-3pbbnz");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			if (if_block0) if_block0.m(div2, null);
			append_hydration(div2, t0);
			append_hydration(div2, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t1);
			append_hydration(div1, t2);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(div1, t3);
			if (if_block1) if_block1.m(div1, null);
			append_hydration(div2, t4);
			current = true;
		},
		p(ctx, dirty) {
			if (/*teaser*/ ctx[5].image.url) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_1$2(ctx);
					if_block0.c();
					if_block0.m(div2, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if ((!current || dirty & /*teasers*/ 8) && t1_value !== (t1_value = /*teaser*/ ctx[5].title + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*teasers*/ 8) && raw_value !== (raw_value = /*teaser*/ ctx[5].content.html + "")) div0.innerHTML = raw_value;
			if (/*teaser*/ ctx[5].link.url) {
				if (if_block1) {
					if_block1.p(ctx, dirty);

					if (dirty & /*teasers*/ 8) {
						transition_in(if_block1, 1);
					}
				} else {
					if_block1 = create_if_block$3(ctx);
					if_block1.c();
					transition_in(if_block1, 1);
					if_block1.m(div1, null);
				}
			} else if (if_block1) {
				group_outros();

				transition_out(if_block1, 1, 1, () => {
					if_block1 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block1);
			current = true;
		},
		o(local) {
			transition_out(if_block1);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
		}
	};
}

function create_fragment$7(ctx) {
	let div2;
	let section;
	let header;
	let span;
	let t0;
	let t1;
	let h2;
	let t2;
	let t3;
	let div0;
	let t4;
	let t5;
	let div1;
	let current;
	let each_value = /*teasers*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$3(get_each_context$3(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div2 = element("div");
			section = element("section");
			header = element("header");
			span = element("span");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h2 = element("h2");
			t2 = text(/*heading*/ ctx[1]);
			t3 = space();
			div0 = element("div");
			t4 = text(/*subheading*/ ctx[2]);
			t5 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			header = claim_element(section_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			span = claim_element(header_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, /*superhead*/ ctx[0]);
			span_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			h2 = claim_element(header_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t2 = claim_text(h2_nodes, /*heading*/ ctx[1]);
			h2_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t4 = claim_text(div0_nodes, /*subheading*/ ctx[2]);
			div0_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t5 = claim_space(section_nodes);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "superhead");
			attr(h2, "class", "heading");
			attr(div0, "class", "subheading");
			attr(header, "class", "heading-group svelte-3pbbnz");
			attr(div1, "class", "teasers svelte-3pbbnz");
			attr(section, "class", "section-container");
			attr(div2, "class", "section");
			attr(div2, "id", "section-c5024290");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, section);
			append_hydration(section, header);
			append_hydration(header, span);
			append_hydration(span, t0);
			append_hydration(header, t1);
			append_hydration(header, h2);
			append_hydration(h2, t2);
			append_hydration(header, t3);
			append_hydration(header, div0);
			append_hydration(div0, t4);
			append_hydration(section, t5);
			append_hydration(section, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*superhead*/ 1) set_data(t0, /*superhead*/ ctx[0]);
			if (!current || dirty & /*heading*/ 2) set_data(t2, /*heading*/ ctx[1]);
			if (!current || dirty & /*subheading*/ 4) set_data(t4, /*subheading*/ ctx[2]);

			if (dirty & /*teasers*/ 8) {
				each_value = /*teasers*/ ctx[3];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$3(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$3(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div1, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { superhead } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { teasers } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(2, subheading = $$props.subheading);
		if ('teasers' in $$props) $$invalidate(3, teasers = $$props.teasers);
	};

	return [superhead, heading, subheading, teasers, favicon];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			favicon: 4,
			superhead: 0,
			heading: 1,
			subheading: 2,
			teasers: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$4(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i].quote;
	child_ctx[5] = list[i].name;
	child_ctx[6] = list[i].subtitle;
	child_ctx[7] = list[i].image;
	child_ctx[9] = i;
	return child_ctx;
}

// (66:4) {#each testimonials as { quote, name, subtitle, image }
function create_each_block$4(ctx) {
	let li;
	let div0;
	let raw_value = /*quote*/ ctx[4].html + "";
	let div0_data_key_value;
	let t0;
	let div2;
	let img;
	let img_src_value;
	let img_alt_value;
	let t1;
	let div1;
	let span0;
	let t2_value = /*name*/ ctx[5] + "";
	let t2;
	let t3;
	let span1;
	let t4_value = /*subtitle*/ ctx[6] + "";
	let t4;
	let t5;

	return {
		c() {
			li = element("li");
			div0 = element("div");
			t0 = space();
			div2 = element("div");
			img = element("img");
			t1 = space();
			div1 = element("div");
			span0 = element("span");
			t2 = text(t2_value);
			t3 = space();
			span1 = element("span");
			t4 = text(t4_value);
			t5 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			div0 = claim_element(li_nodes, "DIV", { class: true, "data-key": true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			div2 = claim_element(li_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			img = claim_element(div2_nodes, "IMG", { src: true, alt: true, class: true });
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			span0 = claim_element(div1_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t2 = claim_text(span0_nodes, t2_value);
			span0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			span1 = claim_element(div1_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t4 = claim_text(span1_nodes, t4_value);
			span1_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t5 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "quote svelte-585z62");
			attr(div0, "data-key", div0_data_key_value = "testimonials[" + /*i*/ ctx[9] + "].quote");
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[7].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[7].alt);
			attr(img, "class", "svelte-585z62");
			attr(span0, "class", "name svelte-585z62");
			attr(span1, "class", "subtitle svelte-585z62");
			attr(div1, "class", "text svelte-585z62");
			attr(div2, "class", "person svelte-585z62");
			attr(li, "class", "svelte-585z62");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, div0);
			div0.innerHTML = raw_value;
			append_hydration(li, t0);
			append_hydration(li, div2);
			append_hydration(div2, img);
			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, span0);
			append_hydration(span0, t2);
			append_hydration(div1, t3);
			append_hydration(div1, span1);
			append_hydration(span1, t4);
			append_hydration(li, t5);
		},
		p(ctx, dirty) {
			if (dirty & /*testimonials*/ 4 && raw_value !== (raw_value = /*quote*/ ctx[4].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*testimonials*/ 4 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[7].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*testimonials*/ 4 && img_alt_value !== (img_alt_value = /*image*/ ctx[7].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*testimonials*/ 4 && t2_value !== (t2_value = /*name*/ ctx[5] + "")) set_data(t2, t2_value);
			if (dirty & /*testimonials*/ 4 && t4_value !== (t4_value = /*subtitle*/ ctx[6] + "")) set_data(t4, t4_value);
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

function create_fragment$8(ctx) {
	let div1;
	let section;
	let div0;
	let span;
	let t0;
	let t1;
	let h2;
	let t2;
	let t3;
	let ul;
	let each_value = /*testimonials*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$4(get_each_context$4(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			span = element("span");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h2 = element("h2");
			t2 = text(/*heading*/ ctx[1]);
			t3 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span = claim_element(div0_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, /*superhead*/ ctx[0]);
			span_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t2 = claim_text(h2_nodes, /*heading*/ ctx[1]);
			h2_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "superhead");
			attr(h2, "class", "heading");
			attr(div0, "class", "heading-group");
			attr(ul, "class", "svelte-585z62");
			attr(section, "class", "section-container svelte-585z62");
			attr(div1, "class", "section");
			attr(div1, "id", "section-60de18a5");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, span);
			append_hydration(span, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h2);
			append_hydration(h2, t2);
			append_hydration(section, t3);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*superhead*/ 1) set_data(t0, /*superhead*/ ctx[0]);
			if (dirty & /*heading*/ 2) set_data(t2, /*heading*/ ctx[1]);

			if (dirty & /*testimonials*/ 4) {
				each_value = /*testimonials*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$4(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$4(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { superhead } = $$props;
	let { heading } = $$props;
	let { testimonials } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('testimonials' in $$props) $$invalidate(2, testimonials = $$props.testimonials);
	};

	return [superhead, heading, testimonials, favicon];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$8, safe_not_equal, {
			favicon: 3,
			superhead: 0,
			heading: 1,
			testimonials: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$5(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i].icon;
	child_ctx[5] = list[i].title;
	child_ctx[6] = list[i].description;
	return child_ctx;
}

// (120:6) {#each cards as { icon, title, description }}
function create_each_block$5(ctx) {
	let div1;
	let div0;
	let icon;
	let t0;
	let span0;
	let t1_value = /*title*/ ctx[5] + "";
	let t1;
	let t2;
	let span1;
	let t3_value = /*description*/ ctx[6] + "";
	let t3;
	let t4;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[4] } });

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			create_component(icon.$$.fragment);
			t0 = space();
			span0 = element("span");
			t1 = text(t1_value);
			t2 = space();
			span1 = element("span");
			t3 = text(t3_value);
			t4 = space();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			claim_component(icon.$$.fragment, div0_nodes);
			div0_nodes.forEach(detach);
			t0 = claim_space(div1_nodes);
			span0 = claim_element(div1_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t1 = claim_text(span0_nodes, t1_value);
			span0_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			span1 = claim_element(div1_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t3 = claim_text(span1_nodes, t3_value);
			span1_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "icon svelte-iewj14");
			attr(span0, "class", "title svelte-iewj14");
			attr(span1, "class", "description svelte-iewj14");
			attr(div1, "class", "card svelte-iewj14");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			mount_component(icon, div0, null);
			append_hydration(div1, t0);
			append_hydration(div1, span0);
			append_hydration(span0, t1);
			append_hydration(div1, t2);
			append_hydration(div1, span1);
			append_hydration(span1, t3);
			append_hydration(div1, t4);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*cards*/ 4) icon_changes.icon = /*icon*/ ctx[4];
			icon.$set(icon_changes);
			if ((!current || dirty & /*cards*/ 4) && t1_value !== (t1_value = /*title*/ ctx[5] + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*cards*/ 4) && t3_value !== (t3_value = /*description*/ ctx[6] + "")) set_data(t3, t3_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_component(icon);
		}
	};
}

function create_fragment$9(ctx) {
	let div3;
	let svg;
	let path;
	let t0;
	let section;
	let div2;
	let div0;
	let h2;
	let t1;
	let t2;
	let form_1;
	let input;
	let input_placeholder_value;
	let t3;
	let button;
	let t4_value = /*form*/ ctx[1].button_label + "";
	let t4;
	let t5;
	let span;
	let t6_value = /*form*/ ctx[1].footer + "";
	let t6;
	let t7;
	let div1;
	let current;
	let each_value = /*cards*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$5(get_each_context$5(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div3 = element("div");
			svg = svg_element("svg");
			path = svg_element("path");
			t0 = space();
			section = element("section");
			div2 = element("div");
			div0 = element("div");
			h2 = element("h2");
			t1 = text(/*heading*/ ctx[0]);
			t2 = space();
			form_1 = element("form");
			input = element("input");
			t3 = space();
			button = element("button");
			t4 = text(t4_value);
			t5 = space();
			span = element("span");
			t6 = text(t6_value);
			t7 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);

			svg = claim_svg_element(div3_nodes, "svg", {
				viewBox: true,
				fill: true,
				xmlns: true,
				class: true
			});

			var svg_nodes = children(svg);

			path = claim_svg_element(svg_nodes, "path", {
				"fill-rule": true,
				"clip-rule": true,
				d: true,
				class: true
			});

			children(path).forEach(detach);
			svg_nodes.forEach(detach);
			t0 = claim_space(div3_nodes);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t1 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			form_1 = claim_element(div0_nodes, "FORM", { action: true, class: true });
			var form_1_nodes = children(form_1);

			input = claim_element(form_1_nodes, "INPUT", {
				type: true,
				placeholder: true,
				class: true
			});

			t3 = claim_space(form_1_nodes);
			button = claim_element(form_1_nodes, "BUTTON", { type: true, class: true });
			var button_nodes = children(button);
			t4 = claim_text(button_nodes, t4_value);
			button_nodes.forEach(detach);
			form_1_nodes.forEach(detach);
			t5 = claim_space(div0_nodes);
			span = claim_element(div0_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t6 = claim_text(span_nodes, t6_value);
			span_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t7 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(path, "fill-rule", "evenodd");
			attr(path, "clip-rule", "evenodd");
			attr(path, "d", "M1440 175H0V0C240 53.3333 480 80 720 80C960 80 1200 53.3333 1440 0V175Z");
			attr(path, "class", "svelte-iewj14");
			attr(svg, "viewBox", "0 0 1440 175");
			attr(svg, "fill", "none");
			attr(svg, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg, "class", "svelte-iewj14");
			attr(h2, "class", "heading");
			attr(input, "type", "email");
			attr(input, "placeholder", input_placeholder_value = /*form*/ ctx[1].placeholder);
			attr(input, "class", "svelte-iewj14");
			attr(button, "type", "button");
			attr(button, "class", "svelte-iewj14");
			attr(form_1, "action", "");
			attr(form_1, "class", "svelte-iewj14");
			attr(span, "class", "footer svelte-iewj14");
			attr(div0, "class", "signup svelte-iewj14");
			attr(div1, "class", "cards svelte-iewj14");
			attr(div2, "class", "section-container svelte-iewj14");
			attr(section, "class", "svelte-iewj14");
			attr(div3, "class", "section");
			attr(div3, "id", "section-1c137d6e");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, svg);
			append_hydration(svg, path);
			append_hydration(div3, t0);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t1);
			append_hydration(div0, t2);
			append_hydration(div0, form_1);
			append_hydration(form_1, input);
			append_hydration(form_1, t3);
			append_hydration(form_1, button);
			append_hydration(button, t4);
			append_hydration(div0, t5);
			append_hydration(div0, span);
			append_hydration(span, t6);
			append_hydration(div2, t7);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t1, /*heading*/ ctx[0]);

			if (!current || dirty & /*form*/ 2 && input_placeholder_value !== (input_placeholder_value = /*form*/ ctx[1].placeholder)) {
				attr(input, "placeholder", input_placeholder_value);
			}

			if ((!current || dirty & /*form*/ 2) && t4_value !== (t4_value = /*form*/ ctx[1].button_label + "")) set_data(t4, t4_value);
			if ((!current || dirty & /*form*/ 2) && t6_value !== (t6_value = /*form*/ ctx[1].footer + "")) set_data(t6, t6_value);

			if (dirty & /*cards*/ 4) {
				each_value = /*cards*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$5(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$5(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div1, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$9($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { heading } = $$props;
	let { form } = $$props;
	let { cards } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('form' in $$props) $$invalidate(1, form = $$props.form);
		if ('cards' in $$props) $$invalidate(2, cards = $$props.cards);
	};

	return [heading, form, cards, favicon];
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$9, create_fragment$9, safe_not_equal, {
			favicon: 3,
			heading: 0,
			form: 1,
			cards: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$6(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	child_ctx[4] = list[i].icon;
	return child_ctx;
}

function get_each_context_1$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	return child_ctx;
}

// (64:6) {#each footer_nav as { link }}
function create_each_block_1$2(ctx) {
	let a;
	let t_value = /*link*/ ctx[3].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*footer_nav*/ 1 && t_value !== (t_value = /*link*/ ctx[3].label + "")) set_data(t, t_value);

			if (dirty & /*footer_nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (70:6) {#each social as { link, icon }}
function create_each_block$6(ctx) {
	let li;
	let a;
	let icon;
	let a_href_value;
	let a_aria_label_value;
	let t;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[4] } });

	return {
		c() {
			li = element("li");
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);

			a = claim_element(li_nodes, "A", {
				href: true,
				"aria-label": true,
				class: true
			});

			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			a_nodes.forEach(detach);
			t = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(a, "aria-label", a_aria_label_value = /*icon*/ ctx[4]);
			attr(a, "class", "svelte-5m5swo");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			mount_component(icon, a, null);
			append_hydration(li, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 2) icon_changes.icon = /*icon*/ ctx[4];
			icon.$set(icon_changes);

			if (!current || dirty & /*social*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*social*/ 2 && a_aria_label_value !== (a_aria_label_value = /*icon*/ ctx[4])) {
				attr(a, "aria-label", a_aria_label_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$a(ctx) {
	let div1;
	let footer;
	let div0;
	let nav;
	let t0;
	let span;
	let a;
	let t1;
	let t2;
	let t3;
	let ul;
	let current;
	let each_value_1 = /*footer_nav*/ ctx[0];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$2(get_each_context_1$2(ctx, each_value_1, i));
	}

	let each_value = /*social*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$6(get_each_context$6(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div1 = element("div");
			footer = element("footer");
			div0 = element("div");
			nav = element("nav");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t0 = space();
			span = element("span");
			a = element("a");
			t1 = text("Primo");
			t2 = text(" Powered");
			t3 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			footer = claim_element(div1_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div0 = claim_element(footer_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			span = claim_element(div0_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			a = claim_element(span_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t1 = claim_text(a_nodes, "Primo");
			a_nodes.forEach(detach);
			t2 = claim_text(span_nodes, " Powered");
			span_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			ul = claim_element(div0_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav, "class", "svelte-5m5swo");
			attr(a, "href", "https://primo.so");
			attr(a, "class", "svelte-5m5swo");
			attr(span, "class", "primo svelte-5m5swo");
			attr(ul, "class", "svelte-5m5swo");
			attr(div0, "class", "section-container svelte-5m5swo");
			attr(footer, "class", "svelte-5m5swo");
			attr(div1, "class", "section");
			attr(div1, "id", "section-24335c74");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, footer);
			append_hydration(footer, div0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(nav, null);
				}
			}

			append_hydration(div0, t0);
			append_hydration(div0, span);
			append_hydration(span, a);
			append_hydration(a, t1);
			append_hydration(span, t2);
			append_hydration(div0, t3);
			append_hydration(div0, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (dirty & /*footer_nav*/ 1) {
				each_value_1 = /*footer_nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$2(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1$2(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(nav, null);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty & /*social*/ 2) {
				each_value = /*social*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$6(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$6(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$a($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { footer_nav } = $$props;
	let { social } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('footer_nav' in $$props) $$invalidate(0, footer_nav = $$props.footer_nav);
		if ('social' in $$props) $$invalidate(1, social = $$props.social);
	};

	return [footer_nav, social, favicon];
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$a, create_fragment$a, safe_not_equal, { favicon: 2, footer_nav: 0, social: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function instance$b($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component$b extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$b, null, safe_not_equal, { favicon: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$b(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let t7;
	let component_8;
	let t8;
	let component_9;
	let t9;
	let component_10;
	let current;

	component_0 = new Component({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				}
			}
		});

	component_1 = new Component$2({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				},
				logo: {
					"size": "8",
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-53' width='169' height='42' viewBox='0 0 169 42' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M50.8601 29.3532H62.8121V25.7532H55.1081V12.1932H50.8601V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M69.8932 26.9532C68.1892 26.9532 67.3012 25.4652 67.3012 23.2332C67.3012 21.0012 68.1892 19.4892 69.8932 19.4892C71.5972 19.4892 72.5092 21.0012 72.5092 23.2332C72.5092 25.4652 71.5972 26.9532 69.8932 26.9532ZM69.9172 29.7372C73.8772 29.7372 76.4692 26.9292 76.4692 23.2332C76.4692 19.5372 73.8772 16.7292 69.9172 16.7292C65.9812 16.7292 63.3412 19.5372 63.3412 23.2332C63.3412 26.9292 65.9812 29.7372 69.9172 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M83.3237 33.6012C85.1477 33.6012 86.7557 33.1932 87.8357 32.2332C88.8197 31.3452 89.4677 30.0012 89.4677 28.1532V17.0652H85.7237V18.3852H85.6757C84.9557 17.3532 83.8517 16.7052 82.2197 16.7052C79.1717 16.7052 77.0597 19.2492 77.0597 22.8492C77.0597 26.6172 79.6277 28.6812 82.3877 28.6812C83.8757 28.6812 84.8117 28.0812 85.5317 27.2652H85.6277V28.4892C85.6277 29.9772 84.9317 30.8412 83.2757 30.8412C81.9797 30.8412 81.3317 30.2892 81.1157 29.6412H77.3237C77.7077 32.2092 79.9397 33.6012 83.3237 33.6012ZM83.2997 25.7772C81.8357 25.7772 80.8757 24.5772 80.8757 22.7292C80.8757 20.8572 81.8357 19.6572 83.2997 19.6572C84.9317 19.6572 85.7957 21.0492 85.7957 22.7052C85.7957 24.4332 85.0037 25.7772 83.2997 25.7772Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M97.166 26.9532C95.462 26.9532 94.574 25.4652 94.574 23.2332C94.574 21.0012 95.462 19.4892 97.166 19.4892C98.87 19.4892 99.782 21.0012 99.782 23.2332C99.782 25.4652 98.87 26.9532 97.166 26.9532ZM97.19 29.7372C101.15 29.7372 103.742 26.9292 103.742 23.2332C103.742 19.5372 101.15 16.7292 97.19 16.7292C93.254 16.7292 90.614 19.5372 90.614 23.2332C90.614 26.9292 93.254 29.7372 97.19 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M104.884 29.3532H108.796V17.0652H104.884V29.3532ZM104.884 15.3612H108.796V12.1932H104.884V15.3612Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M110.494 33.4092H114.406V28.0812H114.454C115.222 29.1132 116.35 29.7372 117.934 29.7372C121.15 29.7372 123.286 27.1932 123.286 23.2092C123.286 19.5132 121.294 16.7052 118.03 16.7052C116.35 16.7052 115.15 17.4492 114.31 18.5532H114.238V17.0652H110.494V33.4092ZM116.926 26.7132C115.246 26.7132 114.286 25.3452 114.286 23.3532C114.286 21.3612 115.15 19.8492 116.854 19.8492C118.534 19.8492 119.326 21.2412 119.326 23.3532C119.326 25.4412 118.414 26.7132 116.926 26.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M129.655 29.7372C132.871 29.7372 135.247 28.3452 135.247 25.6572C135.247 22.5132 132.703 21.9612 130.543 21.6012C128.983 21.3132 127.591 21.1932 127.591 20.3292C127.591 19.5612 128.335 19.2012 129.295 19.2012C130.375 19.2012 131.119 19.5372 131.263 20.6412H134.863C134.671 18.2172 132.799 16.7052 129.319 16.7052C126.415 16.7052 124.015 18.0492 124.015 20.6412C124.015 23.5212 126.295 24.0972 128.431 24.4572C130.063 24.7452 131.551 24.8652 131.551 25.9692C131.551 26.7612 130.807 27.1932 129.631 27.1932C128.335 27.1932 127.519 26.5932 127.375 25.3692H123.679C123.799 28.0812 126.055 29.7372 129.655 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M140.561 29.7132C142.265 29.7132 143.345 29.0412 144.233 27.8412H144.305V29.3532H148.049V17.0652H144.137V23.9292C144.137 25.3932 143.321 26.4012 141.977 26.4012C140.729 26.4012 140.129 25.6572 140.129 24.3132V17.0652H136.241V25.1292C136.241 27.8652 137.729 29.7132 140.561 29.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M149.75 29.3532H153.662V22.4652C153.662 21.0012 154.382 19.9692 155.606 19.9692C156.782 19.9692 157.334 20.7372 157.334 22.0572V29.3532H161.246V22.4652C161.246 21.0012 161.942 19.9692 163.19 19.9692C164.366 19.9692 164.918 20.7372 164.918 22.0572V29.3532H168.83V21.3612C168.83 18.6012 167.438 16.7052 164.654 16.7052C163.07 16.7052 161.75 17.3772 160.79 18.8652H160.742C160.118 17.5452 158.894 16.7052 157.286 16.7052C155.51 16.7052 154.334 17.5452 153.566 18.8172H153.494V17.0652H149.75V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath fill-rule='evenodd' clip-rule='evenodd' d='M20.6842 0.961929C31.946 0.961929 41.0755 10.0914 41.0755 21.3532C41.0755 32.6151 31.946 41.7446 20.6842 41.7446C9.42234 41.7446 0.292847 32.6151 0.292847 21.3532C0.292847 10.0914 9.42234 0.961929 20.6842 0.961929ZM40.2928 21.3532C40.2928 10.5237 31.5137 1.74455 20.6842 1.74455C19.8106 1.74455 18.9505 1.80167 18.1071 1.91238C18.652 1.86474 19.2034 1.84042 19.7606 1.84042C30.1088 1.84042 38.4977 10.2293 38.4977 20.5775C38.4977 30.9256 30.1088 39.3145 19.7606 39.3145C9.96366 39.3145 1.92284 31.7956 1.09401 22.2135C1.54426 32.6439 10.1428 40.9619 20.6842 40.9619C31.5137 40.9619 40.2928 32.1828 40.2928 21.3532ZM37.715 20.5775C37.715 10.6615 29.6766 2.62305 19.7606 2.62305C18.9555 2.62305 18.1627 2.67605 17.3856 2.77874C17.8641 2.73848 18.3482 2.71794 18.8371 2.71794C28.2717 2.71794 35.9199 10.3662 35.9199 19.8007C35.9199 29.2353 28.2717 36.8835 18.8371 36.8835C9.91648 36.8835 2.59287 30.0458 1.8215 21.3256C2.21369 30.8946 10.0953 38.5319 19.7606 38.5319C29.6766 38.5319 37.715 30.4934 37.715 20.5775ZM18.8371 3.50057C27.8394 3.50057 35.1373 10.7984 35.1373 19.8007C35.1373 28.803 27.8394 36.1008 18.8371 36.1008C10.0434 36.1008 2.87602 29.1372 2.54867 20.4235C3.25542 28.2885 9.86471 34.4524 17.9137 34.4524C26.434 34.4524 33.3412 27.5453 33.3412 19.0249C33.3412 10.5045 26.434 3.59741 17.9137 3.59741C17.4729 3.59741 17.0364 3.6159 16.605 3.65213C17.3348 3.5522 18.0799 3.50057 18.8371 3.50057ZM32.5585 19.0249C32.5585 10.9368 26.0018 4.38004 17.9137 4.38004C17.2303 4.38004 16.5578 4.42684 15.8994 4.51742C16.2589 4.48928 16.6223 4.47495 16.9891 4.47495C24.5959 4.47495 30.7624 10.6414 30.7624 18.2482C30.7624 25.8549 24.5959 32.0214 16.9891 32.0214C9.82947 32.0214 3.94576 26.5585 3.27885 19.5736C3.56738 27.4075 10.0092 33.6698 17.9137 33.6698C26.0018 33.6698 32.5585 27.1131 32.5585 19.0249ZM16.9891 5.25757C24.1636 5.25757 29.9797 11.0737 29.9797 18.2482C29.9797 25.4227 24.1636 31.2388 16.9891 31.2388C9.95594 31.2388 4.2282 25.6496 4.00526 18.6706C4.60739 24.8008 9.77718 29.5904 16.0656 29.5904C22.7588 29.5904 28.1846 24.1645 28.1846 17.4714C28.1846 10.7783 22.7588 5.35246 16.0656 5.35246C15.7587 5.35246 15.4544 5.36387 15.1532 5.38629C15.753 5.30145 16.3659 5.25757 16.9891 5.25757ZM27.402 17.4714C27.402 11.2105 22.3265 6.13509 16.0656 6.13509C15.4941 6.13509 14.9325 6.17738 14.3837 6.259C14.6342 6.24106 14.8871 6.23193 15.1422 6.23193C20.9211 6.23193 25.6059 10.9167 25.6059 16.6956C25.6059 22.4746 20.9211 27.1593 15.1422 27.1593C9.72697 27.1593 5.27257 23.0458 4.73324 17.773C4.89313 23.8945 9.90561 28.8078 16.0656 28.8078C22.3265 28.8078 27.402 23.7323 27.402 17.4714ZM15.1422 7.01456C20.4889 7.01456 24.8232 11.3489 24.8232 16.6956C24.8232 22.0424 20.4889 26.3767 15.1422 26.3767C9.86348 26.3767 5.57156 22.152 5.46317 16.8993C5.9508 21.3032 9.68475 24.7283 14.2187 24.7283C19.084 24.7283 23.0281 20.7842 23.0281 15.9189C23.0281 11.0536 19.084 7.10945 14.2187 7.10945C14.0326 7.10945 13.8479 7.11522 13.6647 7.12659C14.1464 7.05282 14.6398 7.01456 15.1422 7.01456ZM22.2455 15.9189C22.2455 11.4858 18.6518 7.89208 14.2187 7.89208C13.7735 7.89208 13.3368 7.92832 12.9113 7.99801C13.0381 7.99133 13.1657 7.98795 13.2942 7.98795C17.2458 7.98795 20.4493 11.1914 20.4493 15.1431C20.4493 19.0948 17.2458 22.2983 13.2942 22.2983C9.64023 22.2983 6.626 19.5593 6.19252 16.0225C6.24802 20.4079 9.8202 23.9457 14.2187 23.9457C18.6518 23.9457 22.2455 20.352 22.2455 15.9189ZM13.2942 8.77057C16.8136 8.77057 19.6667 11.6236 19.6667 15.1431C19.6667 18.6626 16.8136 21.5156 13.2942 21.5156C9.77471 21.5156 6.92163 18.6626 6.92163 15.1431C6.92163 15.1347 6.92165 15.1262 6.92168 15.1178C7.2881 17.7998 9.58806 19.8663 12.3707 19.8663C15.4082 19.8663 17.8706 17.4039 17.8706 14.3664C17.8706 11.3288 15.4082 8.86646 12.3707 8.86646C12.302 8.86646 12.2336 8.86771 12.1655 8.87021C12.5318 8.80474 12.909 8.77057 13.2942 8.77057ZM17.0879 14.3664C17.0879 11.7611 14.976 9.64908 12.3707 9.64908C9.7654 9.64908 7.6534 11.7611 7.6534 14.3664C7.6534 16.9716 9.7654 19.0836 12.3707 19.0836C14.976 19.0836 17.0879 16.9716 17.0879 14.3664Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-53' width='169' height='42' viewBox='0 0 169 42' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M50.8601 29.3532H62.8121V25.7532H55.1081V12.1932H50.8601V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M69.8932 26.9532C68.1892 26.9532 67.3012 25.4652 67.3012 23.2332C67.3012 21.0012 68.1892 19.4892 69.8932 19.4892C71.5972 19.4892 72.5092 21.0012 72.5092 23.2332C72.5092 25.4652 71.5972 26.9532 69.8932 26.9532ZM69.9172 29.7372C73.8772 29.7372 76.4692 26.9292 76.4692 23.2332C76.4692 19.5372 73.8772 16.7292 69.9172 16.7292C65.9812 16.7292 63.3412 19.5372 63.3412 23.2332C63.3412 26.9292 65.9812 29.7372 69.9172 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M83.3237 33.6012C85.1477 33.6012 86.7557 33.1932 87.8357 32.2332C88.8197 31.3452 89.4677 30.0012 89.4677 28.1532V17.0652H85.7237V18.3852H85.6757C84.9557 17.3532 83.8517 16.7052 82.2197 16.7052C79.1717 16.7052 77.0597 19.2492 77.0597 22.8492C77.0597 26.6172 79.6277 28.6812 82.3877 28.6812C83.8757 28.6812 84.8117 28.0812 85.5317 27.2652H85.6277V28.4892C85.6277 29.9772 84.9317 30.8412 83.2757 30.8412C81.9797 30.8412 81.3317 30.2892 81.1157 29.6412H77.3237C77.7077 32.2092 79.9397 33.6012 83.3237 33.6012ZM83.2997 25.7772C81.8357 25.7772 80.8757 24.5772 80.8757 22.7292C80.8757 20.8572 81.8357 19.6572 83.2997 19.6572C84.9317 19.6572 85.7957 21.0492 85.7957 22.7052C85.7957 24.4332 85.0037 25.7772 83.2997 25.7772Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M97.166 26.9532C95.462 26.9532 94.574 25.4652 94.574 23.2332C94.574 21.0012 95.462 19.4892 97.166 19.4892C98.87 19.4892 99.782 21.0012 99.782 23.2332C99.782 25.4652 98.87 26.9532 97.166 26.9532ZM97.19 29.7372C101.15 29.7372 103.742 26.9292 103.742 23.2332C103.742 19.5372 101.15 16.7292 97.19 16.7292C93.254 16.7292 90.614 19.5372 90.614 23.2332C90.614 26.9292 93.254 29.7372 97.19 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M104.884 29.3532H108.796V17.0652H104.884V29.3532ZM104.884 15.3612H108.796V12.1932H104.884V15.3612Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M110.494 33.4092H114.406V28.0812H114.454C115.222 29.1132 116.35 29.7372 117.934 29.7372C121.15 29.7372 123.286 27.1932 123.286 23.2092C123.286 19.5132 121.294 16.7052 118.03 16.7052C116.35 16.7052 115.15 17.4492 114.31 18.5532H114.238V17.0652H110.494V33.4092ZM116.926 26.7132C115.246 26.7132 114.286 25.3452 114.286 23.3532C114.286 21.3612 115.15 19.8492 116.854 19.8492C118.534 19.8492 119.326 21.2412 119.326 23.3532C119.326 25.4412 118.414 26.7132 116.926 26.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M129.655 29.7372C132.871 29.7372 135.247 28.3452 135.247 25.6572C135.247 22.5132 132.703 21.9612 130.543 21.6012C128.983 21.3132 127.591 21.1932 127.591 20.3292C127.591 19.5612 128.335 19.2012 129.295 19.2012C130.375 19.2012 131.119 19.5372 131.263 20.6412H134.863C134.671 18.2172 132.799 16.7052 129.319 16.7052C126.415 16.7052 124.015 18.0492 124.015 20.6412C124.015 23.5212 126.295 24.0972 128.431 24.4572C130.063 24.7452 131.551 24.8652 131.551 25.9692C131.551 26.7612 130.807 27.1932 129.631 27.1932C128.335 27.1932 127.519 26.5932 127.375 25.3692H123.679C123.799 28.0812 126.055 29.7372 129.655 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M140.561 29.7132C142.265 29.7132 143.345 29.0412 144.233 27.8412H144.305V29.3532H148.049V17.0652H144.137V23.9292C144.137 25.3932 143.321 26.4012 141.977 26.4012C140.729 26.4012 140.129 25.6572 140.129 24.3132V17.0652H136.241V25.1292C136.241 27.8652 137.729 29.7132 140.561 29.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M149.75 29.3532H153.662V22.4652C153.662 21.0012 154.382 19.9692 155.606 19.9692C156.782 19.9692 157.334 20.7372 157.334 22.0572V29.3532H161.246V22.4652C161.246 21.0012 161.942 19.9692 163.19 19.9692C164.366 19.9692 164.918 20.7372 164.918 22.0572V29.3532H168.83V21.3612C168.83 18.6012 167.438 16.7052 164.654 16.7052C163.07 16.7052 161.75 17.3772 160.79 18.8652H160.742C160.118 17.5452 158.894 16.7052 157.286 16.7052C155.51 16.7052 154.334 17.5452 153.566 18.8172H153.494V17.0652H149.75V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath fill-rule='evenodd' clip-rule='evenodd' d='M20.6842 0.961929C31.946 0.961929 41.0755 10.0914 41.0755 21.3532C41.0755 32.6151 31.946 41.7446 20.6842 41.7446C9.42234 41.7446 0.292847 32.6151 0.292847 21.3532C0.292847 10.0914 9.42234 0.961929 20.6842 0.961929ZM40.2928 21.3532C40.2928 10.5237 31.5137 1.74455 20.6842 1.74455C19.8106 1.74455 18.9505 1.80167 18.1071 1.91238C18.652 1.86474 19.2034 1.84042 19.7606 1.84042C30.1088 1.84042 38.4977 10.2293 38.4977 20.5775C38.4977 30.9256 30.1088 39.3145 19.7606 39.3145C9.96366 39.3145 1.92284 31.7956 1.09401 22.2135C1.54426 32.6439 10.1428 40.9619 20.6842 40.9619C31.5137 40.9619 40.2928 32.1828 40.2928 21.3532ZM37.715 20.5775C37.715 10.6615 29.6766 2.62305 19.7606 2.62305C18.9555 2.62305 18.1627 2.67605 17.3856 2.77874C17.8641 2.73848 18.3482 2.71794 18.8371 2.71794C28.2717 2.71794 35.9199 10.3662 35.9199 19.8007C35.9199 29.2353 28.2717 36.8835 18.8371 36.8835C9.91648 36.8835 2.59287 30.0458 1.8215 21.3256C2.21369 30.8946 10.0953 38.5319 19.7606 38.5319C29.6766 38.5319 37.715 30.4934 37.715 20.5775ZM18.8371 3.50057C27.8394 3.50057 35.1373 10.7984 35.1373 19.8007C35.1373 28.803 27.8394 36.1008 18.8371 36.1008C10.0434 36.1008 2.87602 29.1372 2.54867 20.4235C3.25542 28.2885 9.86471 34.4524 17.9137 34.4524C26.434 34.4524 33.3412 27.5453 33.3412 19.0249C33.3412 10.5045 26.434 3.59741 17.9137 3.59741C17.4729 3.59741 17.0364 3.6159 16.605 3.65213C17.3348 3.5522 18.0799 3.50057 18.8371 3.50057ZM32.5585 19.0249C32.5585 10.9368 26.0018 4.38004 17.9137 4.38004C17.2303 4.38004 16.5578 4.42684 15.8994 4.51742C16.2589 4.48928 16.6223 4.47495 16.9891 4.47495C24.5959 4.47495 30.7624 10.6414 30.7624 18.2482C30.7624 25.8549 24.5959 32.0214 16.9891 32.0214C9.82947 32.0214 3.94576 26.5585 3.27885 19.5736C3.56738 27.4075 10.0092 33.6698 17.9137 33.6698C26.0018 33.6698 32.5585 27.1131 32.5585 19.0249ZM16.9891 5.25757C24.1636 5.25757 29.9797 11.0737 29.9797 18.2482C29.9797 25.4227 24.1636 31.2388 16.9891 31.2388C9.95594 31.2388 4.2282 25.6496 4.00526 18.6706C4.60739 24.8008 9.77718 29.5904 16.0656 29.5904C22.7588 29.5904 28.1846 24.1645 28.1846 17.4714C28.1846 10.7783 22.7588 5.35246 16.0656 5.35246C15.7587 5.35246 15.4544 5.36387 15.1532 5.38629C15.753 5.30145 16.3659 5.25757 16.9891 5.25757ZM27.402 17.4714C27.402 11.2105 22.3265 6.13509 16.0656 6.13509C15.4941 6.13509 14.9325 6.17738 14.3837 6.259C14.6342 6.24106 14.8871 6.23193 15.1422 6.23193C20.9211 6.23193 25.6059 10.9167 25.6059 16.6956C25.6059 22.4746 20.9211 27.1593 15.1422 27.1593C9.72697 27.1593 5.27257 23.0458 4.73324 17.773C4.89313 23.8945 9.90561 28.8078 16.0656 28.8078C22.3265 28.8078 27.402 23.7323 27.402 17.4714ZM15.1422 7.01456C20.4889 7.01456 24.8232 11.3489 24.8232 16.6956C24.8232 22.0424 20.4889 26.3767 15.1422 26.3767C9.86348 26.3767 5.57156 22.152 5.46317 16.8993C5.9508 21.3032 9.68475 24.7283 14.2187 24.7283C19.084 24.7283 23.0281 20.7842 23.0281 15.9189C23.0281 11.0536 19.084 7.10945 14.2187 7.10945C14.0326 7.10945 13.8479 7.11522 13.6647 7.12659C14.1464 7.05282 14.6398 7.01456 15.1422 7.01456ZM22.2455 15.9189C22.2455 11.4858 18.6518 7.89208 14.2187 7.89208C13.7735 7.89208 13.3368 7.92832 12.9113 7.99801C13.0381 7.99133 13.1657 7.98795 13.2942 7.98795C17.2458 7.98795 20.4493 11.1914 20.4493 15.1431C20.4493 19.0948 17.2458 22.2983 13.2942 22.2983C9.64023 22.2983 6.626 19.5593 6.19252 16.0225C6.24802 20.4079 9.8202 23.9457 14.2187 23.9457C18.6518 23.9457 22.2455 20.352 22.2455 15.9189ZM13.2942 8.77057C16.8136 8.77057 19.6667 11.6236 19.6667 15.1431C19.6667 18.6626 16.8136 21.5156 13.2942 21.5156C9.77471 21.5156 6.92163 18.6626 6.92163 15.1431C6.92163 15.1347 6.92165 15.1262 6.92168 15.1178C7.2881 17.7998 9.58806 19.8663 12.3707 19.8663C15.4082 19.8663 17.8706 17.4039 17.8706 14.3664C17.8706 11.3288 15.4082 8.86646 12.3707 8.86646C12.302 8.86646 12.2336 8.86771 12.1655 8.87021C12.5318 8.80474 12.909 8.77057 13.2942 8.77057ZM17.0879 14.3664C17.0879 11.7611 14.976 9.64908 12.3707 9.64908C9.7654 9.64908 7.6534 11.7611 7.6534 14.3664C7.6534 16.9716 9.7654 19.0836 12.3707 19.0836C14.976 19.0836 17.0879 16.9716 17.0879 14.3664Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/", "label": "Product" }
					},
					{ "link": { "url": "/", "label": "Why" } },
					{
						"link": { "url": "/", "label": "Pricing" }
					}
				],
				cta: [
					{
						"link": { "url": "/", "label": "Sign up" }
					}
				]
			}
		});

	component_2 = new Component$3({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				},
				heading: "Schedule Meetings in Minutes with Cali",
				subheading: "Get your meetings effortlessly organized with Cali. So you can spend more time on meeting people instead of scheduling meetings.",
				link: { "url": "/", "label": "Schedule a demo" },
				image: {
					"alt": "",
					"src": "https://images.unsplash.com/photo-1557804506-669a67965ba0?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1674&q=80",
					"url": "https://images.unsplash.com/photo-1557804506-669a67965ba0?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1674&q=80",
					"size": null
				},
				variation: ""
			}
		});

	component_3 = new Component$4({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				},
				superhead: "Scheduling Infrastructure",
				heading: "Focus on meeting,<br>not scheduling meetings.",
				subhead: "",
				icon_list: [
					{
						"icon": "akar-icons:circle-check-fill",
						"label": "Open source"
					},
					{
						"icon": "akar-icons:circle-check-fill",
						"label": "Free for individuals"
					},
					{
						"icon": "akar-icons:circle-check-fill",
						"label": "\nSafe and secure\n"
					}
				],
				cards: [
					{
						"icon": "material-symbols:check-circle-outline-rounded",
						"link": { "url": "/", "label": "Learn More" },
						"title": "Workflow automation",
						"content": {
							"html": "<p>Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.</p>",
							"markdown": "Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.\n\n"
						}
					},
					{
						"icon": "akar-icons:calendar",
						"link": { "url": "/", "label": "Learn More" },
						"title": "Connect your calendar(s)",
						"content": {
							"html": "<p>Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur.</p>",
							"markdown": "Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur.\n\n"
						}
					},
					{
						"icon": "akar-icons:book",
						"link": { "url": "/", "label": "Learn More" },
						"title": "Double-sided booking",
						"content": {
							"html": "<p>Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat.</p>",
							"markdown": "Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat.\n\n"
						}
					}
				]
			}
		});

	component_4 = new Component$5({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				},
				superhead: "Our Partners",
				heading: "We've gained the trust of loads of companies.",
				logos: [
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-3' width='132' height='35' viewBox='0 0 132 35' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M44.83 25.2047C44.2352 25.237 43.6469 25.0679 43.16 24.7247C42.9566 24.5739 42.7929 24.3758 42.6831 24.1476C42.5733 23.9193 42.5208 23.6678 42.53 23.4147V14.1447C42.5252 14.1055 42.5293 14.0656 42.5422 14.0282C42.555 13.9908 42.5762 13.9569 42.6042 13.9289C42.6322 13.9009 42.6661 13.8797 42.7035 13.8669C42.7409 13.854 42.7808 13.8499 42.82 13.8547H44.5C44.69 13.8547 44.78 13.9547 44.78 14.1447V22.6947C44.78 23.0747 44.95 23.2647 45.3 23.2647C45.4484 23.2708 45.5968 23.254 45.74 23.2147C45.94 23.2147 46.05 23.2747 46.06 23.4547L46.21 24.7047C46.2172 24.7412 46.2165 24.7787 46.208 24.8149C46.1995 24.851 46.1833 24.885 46.1605 24.9143C46.1378 24.9437 46.109 24.9679 46.0762 24.9852C46.0433 25.0025 46.0071 25.0126 45.97 25.0147C45.602 25.1363 45.2175 25.2004 44.83 25.2047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M54.28 24.1347C53.4359 24.8322 52.375 25.2137 51.28 25.2137C50.185 25.2137 49.1242 24.8322 48.28 24.1347C47.5381 23.3857 47.1218 22.374 47.1218 21.3197C47.1218 20.2654 47.5381 19.2537 48.28 18.5047C49.1258 17.8108 50.186 17.4316 51.28 17.4316C52.374 17.4316 53.4342 17.8108 54.28 18.5047C55.0049 19.2606 55.4096 20.2674 55.4096 21.3147C55.4096 22.362 55.0049 23.3688 54.28 24.1247V24.1347ZM49.86 22.8147C50.2518 23.1696 50.7614 23.3661 51.29 23.3661C51.8186 23.3661 52.3283 23.1696 52.72 22.8147C53.0746 22.4071 53.2698 21.885 53.2698 21.3447C53.2698 20.8045 53.0746 20.2824 52.72 19.8747C52.3283 19.5199 51.8186 19.3233 51.29 19.3233C50.7614 19.3233 50.2518 19.5199 49.86 19.8747C49.5055 20.2824 49.3102 20.8045 49.3102 21.3447C49.3102 21.885 49.5055 22.4071 49.86 22.8147Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M64.66 17.6847C64.85 17.6847 64.94 17.7847 64.94 17.9747V25.1447C64.9575 25.6287 64.8669 26.1104 64.6749 26.5549C64.4829 26.9995 64.1943 27.3957 63.83 27.7147C63.0214 28.4042 61.9816 28.7615 60.92 28.7147C59.9612 28.7484 59.0151 28.4866 58.21 27.9647C57.8662 27.739 57.5725 27.4449 57.3472 27.1009C57.1218 26.7568 56.9696 26.3701 56.9 25.9647C56.9 25.7647 56.9 25.6747 57.17 25.6747H58.85C58.9213 25.6771 58.9905 25.7002 59.049 25.741C59.1076 25.7818 59.1531 25.8386 59.18 25.9047C59.289 26.2084 59.5062 26.4613 59.79 26.6147C60.1359 26.7932 60.5209 26.8826 60.91 26.8747C61.1448 26.8876 61.3798 26.8535 61.6013 26.7745C61.8228 26.6956 62.0263 26.5732 62.2 26.4147C62.3587 26.2489 62.4821 26.0526 62.5629 25.8378C62.6437 25.623 62.6801 25.394 62.67 25.1647V24.5347C62.0685 24.9771 61.3364 25.2059 60.59 25.1847C60.0676 25.2037 59.5468 25.117 59.0587 24.9297C58.5707 24.7423 58.1256 24.4584 57.75 24.0947C57.0291 23.3489 56.6261 22.3521 56.6261 21.3147C56.6261 20.2774 57.0291 19.2806 57.75 18.5347C58.1274 18.1743 58.5731 17.8931 59.0608 17.7076C59.5486 17.5221 60.0685 17.4361 60.59 17.4547C61.358 17.4344 62.1098 17.678 62.72 18.1447V17.9847C62.7154 17.9464 62.7194 17.9075 62.7317 17.8709C62.744 17.8344 62.7643 17.801 62.7911 17.7732C62.8179 17.7454 62.8506 17.724 62.8867 17.7104C62.9229 17.6968 62.9616 17.6915 63 17.6947L64.66 17.6847ZM60.78 23.4047C61.0376 23.4127 61.2939 23.364 61.5306 23.262C61.7673 23.1601 61.9788 23.0074 62.15 22.8147C62.4825 22.3854 62.6629 21.8577 62.6629 21.3147C62.6629 20.7717 62.4825 20.2441 62.15 19.8147C61.9794 19.6247 61.7692 19.4742 61.5343 19.374C61.2993 19.2738 61.0453 19.2263 60.79 19.2347C60.5294 19.2265 60.2702 19.275 60.0302 19.3769C59.7902 19.4788 59.5752 19.6316 59.4 19.8247C59.0317 20.2354 58.838 20.7735 58.86 21.3247C58.842 21.8705 59.0314 22.4029 59.39 22.8147C59.5656 23.0073 59.7807 23.1598 60.0206 23.2616C60.2605 23.3634 60.5195 23.4122 60.78 23.4047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M73.57 24.1347C72.7242 24.8286 71.664 25.2078 70.57 25.2078C69.476 25.2078 68.4158 24.8286 67.57 24.1347C66.8445 23.3771 66.4395 22.3687 66.4395 21.3197C66.4395 20.2708 66.8445 19.2623 67.57 18.5047C68.4166 17.8126 69.4765 17.4345 70.57 17.4345C71.6635 17.4345 72.7234 17.8126 73.57 18.5047C74.2949 19.2606 74.6996 20.2674 74.6996 21.3147C74.6996 22.362 74.2949 23.3688 73.57 24.1247V24.1347ZM69.14 22.8147C69.3317 22.9971 69.5577 23.1396 69.8049 23.234C70.0521 23.3284 70.3155 23.3729 70.58 23.3647C70.8428 23.3715 71.1044 23.3265 71.3498 23.2321C71.5952 23.1377 71.8195 22.9959 72.01 22.8147C72.3588 22.4043 72.5503 21.8833 72.5503 21.3447C72.5503 20.8061 72.3588 20.2851 72.01 19.8747C71.8195 19.6936 71.5952 19.5517 71.3498 19.4574C71.1044 19.363 70.8428 19.3179 70.58 19.3247C70.3155 19.3166 70.0521 19.361 69.8049 19.4554C69.5577 19.5498 69.3317 19.6924 69.14 19.8747C68.7913 20.2851 68.5998 20.8061 68.5998 21.3447C68.5998 21.8833 68.7913 22.4043 69.14 22.8147Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M78.31 15.9847C78.0457 16.2161 77.7063 16.3436 77.355 16.3436C77.0037 16.3436 76.6644 16.2161 76.4 15.9847C76.2802 15.8716 76.1847 15.7352 76.1194 15.5839C76.0542 15.4326 76.0205 15.2695 76.0205 15.1047C76.0205 14.9399 76.0542 14.7769 76.1194 14.6255C76.1847 14.4742 76.2802 14.3378 76.4 14.2247C76.6671 13.9991 77.0054 13.8754 77.355 13.8754C77.7046 13.8754 78.0429 13.9991 78.31 14.2247C78.4299 14.3378 78.5254 14.4742 78.5906 14.6255C78.6559 14.7769 78.6895 14.9399 78.6895 15.1047C78.6895 15.2695 78.6559 15.4326 78.5906 15.5839C78.5254 15.7352 78.4299 15.8716 78.31 15.9847ZM78.52 25.2047C77.9256 25.2339 77.3383 25.0651 76.85 24.7247C76.6497 24.5717 76.4888 24.3729 76.381 24.145C76.2731 23.9171 76.2213 23.6667 76.23 23.4147V17.9747C76.2252 17.9355 76.2293 17.8956 76.2422 17.8582C76.255 17.8208 76.2762 17.7869 76.3042 17.7589C76.3322 17.7309 76.3661 17.7097 76.4035 17.6969C76.4409 17.684 76.4808 17.6799 76.52 17.6847H78.2C78.39 17.6847 78.48 17.7847 78.48 17.9747V22.6947C78.48 23.0747 78.65 23.2647 78.99 23.2647C79.1417 23.2702 79.2933 23.2533 79.44 23.2147C79.64 23.2147 79.75 23.2747 79.76 23.4547L79.91 24.7047C79.9172 24.7412 79.9165 24.7787 79.908 24.8149C79.8995 24.851 79.8833 24.885 79.8605 24.9143C79.8378 24.9437 79.809 24.9679 79.7762 24.9852C79.7433 25.0025 79.7071 25.0126 79.67 25.0147C79.2988 25.137 78.9109 25.2011 78.52 25.2047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M86.09 17.4447C86.6148 17.424 87.1383 17.5089 87.6296 17.6944C88.1209 17.88 88.57 18.1623 88.95 18.5247C89.6572 19.2837 90.0504 20.2824 90.0504 21.3197C90.0504 22.357 89.6572 23.3558 88.95 24.1147C88.5718 24.4804 88.1233 24.7655 87.6317 24.9528C87.1401 25.1402 86.6157 25.2259 86.09 25.2047C85.3412 25.2214 84.6073 24.9932 84 24.5547V28.1647C84 28.3547 83.9 28.4447 83.71 28.4447H82.03C81.9917 28.4519 81.9522 28.4496 81.9149 28.4381C81.8777 28.4265 81.8438 28.4061 81.8162 28.3785C81.7887 28.3509 81.7682 28.3171 81.7567 28.2798C81.7451 28.2426 81.7429 28.2031 81.75 28.1647V19.9647C81.7618 19.8845 81.7546 19.8027 81.7292 19.7257C81.7037 19.6488 81.6605 19.5788 81.6032 19.5215C81.5459 19.4642 81.476 19.4211 81.399 19.3956C81.3221 19.3701 81.2402 19.363 81.16 19.3747H80.83C80.61 19.3747 80.5 19.2947 80.5 19.1347V17.9547C80.4948 17.8817 80.5148 17.8091 80.5567 17.7491C80.5985 17.689 80.6597 17.6451 80.73 17.6247C81.0759 17.499 81.442 17.438 81.81 17.4447C82.177 17.4122 82.5453 17.4901 82.8678 17.6682C83.1902 17.8464 83.4522 18.1168 83.62 18.4447C83.9421 18.1189 84.3273 17.8622 84.752 17.6902C85.1767 17.5183 85.632 17.4347 86.09 17.4447ZM84.53 22.8147C84.7083 23.0011 84.9225 23.1494 85.1597 23.2507C85.3969 23.352 85.6521 23.4042 85.91 23.4042C86.1679 23.4042 86.4232 23.352 86.6603 23.2507C86.8975 23.1494 87.1117 23.0011 87.29 22.8147C87.6656 22.3958 87.8629 21.8469 87.84 21.2847C87.8662 20.7221 87.6684 20.1719 87.29 19.7547C87.1117 19.5684 86.8975 19.4201 86.6603 19.3188C86.4232 19.2174 86.1679 19.1652 85.91 19.1652C85.6521 19.1652 85.3969 19.2174 85.1597 19.3188C84.9225 19.4201 84.7083 19.5684 84.53 19.7547C84.1662 20.1793 83.9768 20.726 84 21.2847C83.9797 21.843 84.1688 22.3887 84.53 22.8147Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M94.77 25.2047C93.8723 25.2416 92.9822 25.0269 92.2 24.5847C91.8862 24.3957 91.619 24.1384 91.4181 23.832C91.2173 23.5256 91.0881 23.1779 91.04 22.8147C91.04 22.6147 91.11 22.5147 91.33 22.5147H92.8C92.8699 22.5175 92.9378 22.5394 92.996 22.5783C93.0542 22.6171 93.1006 22.6712 93.13 22.7347C93.34 23.2747 93.89 23.5447 94.77 23.5447C95.077 23.5588 95.3826 23.4969 95.66 23.3647C95.7558 23.3215 95.8379 23.2531 95.8978 23.1668C95.9577 23.0805 95.993 22.9795 96 22.8747C96 22.6147 95.84 22.4347 95.52 22.3147C95.1405 22.1884 94.7481 22.1045 94.35 22.0647C93.8785 22.0113 93.4109 21.9278 92.95 21.8147C92.5018 21.7133 92.0943 21.4799 91.78 21.1447C91.5949 20.9169 91.4587 20.6534 91.3797 20.3707C91.3008 20.088 91.2809 19.792 91.3212 19.5013C91.3616 19.2105 91.4613 18.9311 91.6142 18.6806C91.7671 18.43 91.9699 18.2136 92.21 18.0447C92.9308 17.5856 93.7765 17.3619 94.63 17.4047C95.4564 17.3768 96.274 17.5812 96.99 17.9947C97.2786 18.1582 97.527 18.3839 97.7173 18.6555C97.9076 18.9271 98.0349 19.2377 98.09 19.5647C98.09 19.7647 98 19.8647 97.82 19.8647H96.34C96.2777 19.8684 96.2157 19.8532 96.1622 19.8211C96.1087 19.789 96.0661 19.7414 96.04 19.6847C95.9411 19.4479 95.7549 19.2581 95.52 19.1547C95.255 19.0161 94.959 18.9472 94.66 18.9547C94.3669 18.9388 94.0745 18.9973 93.81 19.1247C93.7168 19.1607 93.6366 19.2237 93.5795 19.3057C93.5225 19.3877 93.4913 19.4849 93.49 19.5847C93.4964 19.7215 93.5465 19.8526 93.6329 19.9588C93.7193 20.065 93.8374 20.1406 93.97 20.1747C94.354 20.3195 94.7533 20.4201 95.16 20.4747C95.6277 20.5363 96.0917 20.6231 96.55 20.7347C96.9982 20.8362 97.4057 21.0695 97.72 21.4047C97.8882 21.5894 98.018 21.8055 98.1021 22.0407C98.1862 22.2758 98.2229 22.5253 98.21 22.7747C98.2186 23.1204 98.1375 23.4624 97.9745 23.7674C97.8115 24.0723 97.5722 24.3298 97.28 24.5147C96.5329 24.9944 95.6574 25.235 94.77 25.2047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M108.78 24.7047C108.786 24.7402 108.784 24.7765 108.776 24.8114C108.767 24.8464 108.752 24.8792 108.73 24.9081C108.709 24.937 108.682 24.9613 108.651 24.9796C108.62 24.9979 108.586 25.0098 108.55 25.0147C108.185 25.1339 107.804 25.198 107.42 25.2047C107.04 25.2441 106.656 25.1847 106.306 25.0323C105.955 24.8799 105.65 24.6396 105.42 24.3347C104.714 24.942 103.8 25.2536 102.87 25.2047C102.438 25.2246 102.007 25.1539 101.604 24.9972C101.201 24.8405 100.835 24.6012 100.53 24.2947C100.227 23.9736 99.9922 23.5946 99.8392 23.1805C99.6863 22.7664 99.6186 22.3257 99.64 21.8847V17.9747C99.64 17.7847 99.73 17.6847 99.92 17.6847H101.6C101.79 17.6847 101.88 17.7847 101.88 17.9747V21.5847C101.862 22.0345 102.015 22.4743 102.31 22.8147C102.457 22.9707 102.636 23.0933 102.834 23.1744C103.032 23.2555 103.246 23.2931 103.46 23.2847C103.679 23.2943 103.898 23.2604 104.104 23.1848C104.31 23.1093 104.499 22.9937 104.66 22.8447C104.812 22.6877 104.931 22.5011 105.008 22.2964C105.086 22.0917 105.12 21.8733 105.11 21.6547V17.9747C105.11 17.7847 105.2 17.6847 105.39 17.6847H107.09C107.28 17.6847 107.37 17.7847 107.37 17.9747V22.6847C107.37 23.0747 107.54 23.2647 107.87 23.2647C108.025 23.2707 108.18 23.2539 108.33 23.2147C108.368 23.2041 108.408 23.2022 108.446 23.2092C108.485 23.2161 108.521 23.2317 108.553 23.2548C108.585 23.2779 108.611 23.3079 108.63 23.3425C108.648 23.3771 108.658 23.4155 108.66 23.4547L108.78 24.7047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M124.67 24.7047C124.679 24.7405 124.68 24.7779 124.673 24.8141C124.665 24.8502 124.65 24.8844 124.628 24.914C124.606 24.9436 124.578 24.968 124.545 24.9854C124.513 25.0029 124.477 25.0129 124.44 25.0147C124.068 25.1356 123.681 25.1997 123.29 25.2047C122.695 25.2354 122.108 25.0665 121.62 24.7247C121.409 24.5783 121.238 24.3822 121.121 24.1537C121.004 23.9252 120.945 23.6713 120.95 23.4147V21.0647C120.971 20.6163 120.821 20.1766 120.53 19.8347C120.39 19.6784 120.216 19.5552 120.023 19.4739C119.829 19.3927 119.62 19.3554 119.41 19.3647C119.221 19.3576 119.033 19.3935 118.859 19.4697C118.686 19.5459 118.533 19.6605 118.41 19.8047C118.146 20.1398 118.011 20.5586 118.03 20.9847V24.6747C118.03 24.8647 117.94 24.9647 117.75 24.9647H116.06C116.021 24.9696 115.981 24.9654 115.944 24.9526C115.906 24.9397 115.872 24.9185 115.844 24.8905C115.816 24.8626 115.795 24.8286 115.782 24.7912C115.769 24.7538 115.765 24.714 115.77 24.6747V21.0647C115.792 20.6212 115.653 20.1846 115.38 19.8347C115.258 19.6877 115.105 19.5694 114.932 19.4882C114.76 19.407 114.571 19.3648 114.38 19.3647C114.176 19.3565 113.973 19.3914 113.783 19.4673C113.593 19.5431 113.422 19.6581 113.28 19.8047C112.994 20.1291 112.847 20.5529 112.87 20.9847V24.6747C112.875 24.714 112.871 24.7538 112.858 24.7912C112.845 24.8286 112.824 24.8626 112.796 24.8905C112.768 24.9185 112.734 24.9397 112.697 24.9526C112.659 24.9654 112.619 24.9696 112.58 24.9647H110.95C110.76 24.9647 110.67 24.8647 110.67 24.6747V19.9647C110.682 19.8845 110.675 19.8027 110.649 19.7257C110.624 19.6488 110.581 19.5788 110.523 19.5215C110.466 19.4642 110.396 19.4211 110.319 19.3956C110.242 19.3701 110.16 19.363 110.08 19.3747H109.75C109.53 19.3747 109.42 19.2947 109.42 19.1347V17.9547C109.415 17.8817 109.435 17.8091 109.477 17.7491C109.519 17.689 109.58 17.6451 109.65 17.6247C109.996 17.499 110.362 17.438 110.73 17.4447C111.083 17.4146 111.438 17.485 111.753 17.6478C112.068 17.8106 112.33 18.0591 112.51 18.3647C112.847 18.045 113.247 17.7982 113.684 17.6399C114.121 17.4816 114.586 17.4152 115.05 17.4447C115.501 17.4227 115.95 17.5072 116.362 17.6914C116.774 17.8756 117.136 18.1542 117.42 18.5047C117.751 18.145 118.158 17.8634 118.611 17.68C119.064 17.4967 119.552 17.4164 120.04 17.4447C120.476 17.4243 120.912 17.4946 121.32 17.6513C121.728 17.8079 122.099 18.0474 122.41 18.3547C122.714 18.6752 122.949 19.0541 123.102 19.4684C123.255 19.8826 123.323 20.3237 123.3 20.7647V22.6947C123.3 23.0747 123.47 23.2647 123.79 23.2647C123.945 23.2719 124.1 23.2551 124.25 23.2147C124.457 23.2147 124.567 23.2947 124.58 23.4547L124.67 24.7047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M7.41 16.3847C8.14777 13.4194 9.85643 10.7861 12.2639 8.90424C14.6714 7.02234 17.6393 6 20.695 6C23.7507 6 26.7186 7.02234 29.1261 8.90424C31.5336 10.7861 33.2422 13.4194 33.98 16.3847H32.78C30.7557 16.3549 28.7729 16.9599 27.11 18.1147C27.014 18.1842 26.9138 18.2477 26.81 18.3047H26.67C26.5662 18.2477 26.466 18.1842 26.37 18.1147C24.6924 16.9866 22.7166 16.3841 20.695 16.3841C18.6734 16.3841 16.6976 16.9866 15.02 18.1147C14.924 18.1842 14.8238 18.2477 14.72 18.3047H14.58C14.4762 18.2477 14.376 18.1842 14.28 18.1147C12.6171 16.9599 10.6343 16.3549 8.61 16.3847H7.41ZM30.62 22.6547C31.236 22.175 31.9995 21.924 32.78 21.9447H34.39V18.7347H32.78C31.4052 18.7181 30.0619 19.146 28.95 19.9547C28.3243 20.416 27.5674 20.6649 26.79 20.6649C26.0126 20.6649 25.2557 20.416 24.63 19.9547C23.4899 19.1611 22.1341 18.7356 20.745 18.7356C19.3559 18.7356 18.0001 19.1611 16.86 19.9547C16.2343 20.416 15.4774 20.6649 14.7 20.6649C13.9226 20.6649 13.1657 20.416 12.54 19.9547C11.4144 19.1356 10.0518 18.7072 8.66 18.7347H7V21.9447H8.61C9.39051 21.924 10.154 22.175 10.77 22.6547C11.908 23.4489 13.2623 23.8747 14.65 23.8747C16.0377 23.8747 17.392 23.4489 18.53 22.6547C19.1468 22.1765 19.9097 21.9257 20.69 21.9447C21.4708 21.9223 22.2348 22.1735 22.85 22.6547C23.9901 23.4484 25.3459 23.8738 26.735 23.8738C28.1241 23.8738 29.4799 23.4484 30.62 22.6547V22.6547ZM30.62 28.3947C31.236 27.915 31.9995 27.664 32.78 27.6847H34.39V24.4747H32.78C31.4052 24.4581 30.0619 24.886 28.95 25.6947C28.3243 26.156 27.5674 26.4049 26.79 26.4049C26.0126 26.4049 25.2557 26.156 24.63 25.6947C23.4899 24.9011 22.1341 24.4757 20.745 24.4757C19.3559 24.4757 18.0001 24.9011 16.86 25.6947C16.2343 26.156 15.4774 26.4049 14.7 26.4049C13.9226 26.4049 13.1657 26.156 12.54 25.6947C11.4144 24.8757 10.0518 24.4472 8.66 24.4747H7V27.6847H8.61C9.39051 27.664 10.154 27.915 10.77 28.3947C11.908 29.1889 13.2623 29.6147 14.65 29.6147C16.0377 29.6147 17.392 29.1889 18.53 28.3947C19.1468 27.9165 19.9097 27.6657 20.69 27.6847C21.4708 27.6623 22.2348 27.9135 22.85 28.3947C23.9901 29.1884 25.3459 29.6138 26.735 29.6138C28.1241 29.6138 29.4799 29.1884 30.62 28.3947V28.3947Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-3' width='132' height='35' viewBox='0 0 132 35' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M44.83 25.2047C44.2352 25.237 43.6469 25.0679 43.16 24.7247C42.9566 24.5739 42.7929 24.3758 42.6831 24.1476C42.5733 23.9193 42.5208 23.6678 42.53 23.4147V14.1447C42.5252 14.1055 42.5293 14.0656 42.5422 14.0282C42.555 13.9908 42.5762 13.9569 42.6042 13.9289C42.6322 13.9009 42.6661 13.8797 42.7035 13.8669C42.7409 13.854 42.7808 13.8499 42.82 13.8547H44.5C44.69 13.8547 44.78 13.9547 44.78 14.1447V22.6947C44.78 23.0747 44.95 23.2647 45.3 23.2647C45.4484 23.2708 45.5968 23.254 45.74 23.2147C45.94 23.2147 46.05 23.2747 46.06 23.4547L46.21 24.7047C46.2172 24.7412 46.2165 24.7787 46.208 24.8149C46.1995 24.851 46.1833 24.885 46.1605 24.9143C46.1378 24.9437 46.109 24.9679 46.0762 24.9852C46.0433 25.0025 46.0071 25.0126 45.97 25.0147C45.602 25.1363 45.2175 25.2004 44.83 25.2047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M54.28 24.1347C53.4359 24.8322 52.375 25.2137 51.28 25.2137C50.185 25.2137 49.1242 24.8322 48.28 24.1347C47.5381 23.3857 47.1218 22.374 47.1218 21.3197C47.1218 20.2654 47.5381 19.2537 48.28 18.5047C49.1258 17.8108 50.186 17.4316 51.28 17.4316C52.374 17.4316 53.4342 17.8108 54.28 18.5047C55.0049 19.2606 55.4096 20.2674 55.4096 21.3147C55.4096 22.362 55.0049 23.3688 54.28 24.1247V24.1347ZM49.86 22.8147C50.2518 23.1696 50.7614 23.3661 51.29 23.3661C51.8186 23.3661 52.3283 23.1696 52.72 22.8147C53.0746 22.4071 53.2698 21.885 53.2698 21.3447C53.2698 20.8045 53.0746 20.2824 52.72 19.8747C52.3283 19.5199 51.8186 19.3233 51.29 19.3233C50.7614 19.3233 50.2518 19.5199 49.86 19.8747C49.5055 20.2824 49.3102 20.8045 49.3102 21.3447C49.3102 21.885 49.5055 22.4071 49.86 22.8147Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M64.66 17.6847C64.85 17.6847 64.94 17.7847 64.94 17.9747V25.1447C64.9575 25.6287 64.8669 26.1104 64.6749 26.5549C64.4829 26.9995 64.1943 27.3957 63.83 27.7147C63.0214 28.4042 61.9816 28.7615 60.92 28.7147C59.9612 28.7484 59.0151 28.4866 58.21 27.9647C57.8662 27.739 57.5725 27.4449 57.3472 27.1009C57.1218 26.7568 56.9696 26.3701 56.9 25.9647C56.9 25.7647 56.9 25.6747 57.17 25.6747H58.85C58.9213 25.6771 58.9905 25.7002 59.049 25.741C59.1076 25.7818 59.1531 25.8386 59.18 25.9047C59.289 26.2084 59.5062 26.4613 59.79 26.6147C60.1359 26.7932 60.5209 26.8826 60.91 26.8747C61.1448 26.8876 61.3798 26.8535 61.6013 26.7745C61.8228 26.6956 62.0263 26.5732 62.2 26.4147C62.3587 26.2489 62.4821 26.0526 62.5629 25.8378C62.6437 25.623 62.6801 25.394 62.67 25.1647V24.5347C62.0685 24.9771 61.3364 25.2059 60.59 25.1847C60.0676 25.2037 59.5468 25.117 59.0587 24.9297C58.5707 24.7423 58.1256 24.4584 57.75 24.0947C57.0291 23.3489 56.6261 22.3521 56.6261 21.3147C56.6261 20.2774 57.0291 19.2806 57.75 18.5347C58.1274 18.1743 58.5731 17.8931 59.0608 17.7076C59.5486 17.5221 60.0685 17.4361 60.59 17.4547C61.358 17.4344 62.1098 17.678 62.72 18.1447V17.9847C62.7154 17.9464 62.7194 17.9075 62.7317 17.8709C62.744 17.8344 62.7643 17.801 62.7911 17.7732C62.8179 17.7454 62.8506 17.724 62.8867 17.7104C62.9229 17.6968 62.9616 17.6915 63 17.6947L64.66 17.6847ZM60.78 23.4047C61.0376 23.4127 61.2939 23.364 61.5306 23.262C61.7673 23.1601 61.9788 23.0074 62.15 22.8147C62.4825 22.3854 62.6629 21.8577 62.6629 21.3147C62.6629 20.7717 62.4825 20.2441 62.15 19.8147C61.9794 19.6247 61.7692 19.4742 61.5343 19.374C61.2993 19.2738 61.0453 19.2263 60.79 19.2347C60.5294 19.2265 60.2702 19.275 60.0302 19.3769C59.7902 19.4788 59.5752 19.6316 59.4 19.8247C59.0317 20.2354 58.838 20.7735 58.86 21.3247C58.842 21.8705 59.0314 22.4029 59.39 22.8147C59.5656 23.0073 59.7807 23.1598 60.0206 23.2616C60.2605 23.3634 60.5195 23.4122 60.78 23.4047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M73.57 24.1347C72.7242 24.8286 71.664 25.2078 70.57 25.2078C69.476 25.2078 68.4158 24.8286 67.57 24.1347C66.8445 23.3771 66.4395 22.3687 66.4395 21.3197C66.4395 20.2708 66.8445 19.2623 67.57 18.5047C68.4166 17.8126 69.4765 17.4345 70.57 17.4345C71.6635 17.4345 72.7234 17.8126 73.57 18.5047C74.2949 19.2606 74.6996 20.2674 74.6996 21.3147C74.6996 22.362 74.2949 23.3688 73.57 24.1247V24.1347ZM69.14 22.8147C69.3317 22.9971 69.5577 23.1396 69.8049 23.234C70.0521 23.3284 70.3155 23.3729 70.58 23.3647C70.8428 23.3715 71.1044 23.3265 71.3498 23.2321C71.5952 23.1377 71.8195 22.9959 72.01 22.8147C72.3588 22.4043 72.5503 21.8833 72.5503 21.3447C72.5503 20.8061 72.3588 20.2851 72.01 19.8747C71.8195 19.6936 71.5952 19.5517 71.3498 19.4574C71.1044 19.363 70.8428 19.3179 70.58 19.3247C70.3155 19.3166 70.0521 19.361 69.8049 19.4554C69.5577 19.5498 69.3317 19.6924 69.14 19.8747C68.7913 20.2851 68.5998 20.8061 68.5998 21.3447C68.5998 21.8833 68.7913 22.4043 69.14 22.8147Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M78.31 15.9847C78.0457 16.2161 77.7063 16.3436 77.355 16.3436C77.0037 16.3436 76.6644 16.2161 76.4 15.9847C76.2802 15.8716 76.1847 15.7352 76.1194 15.5839C76.0542 15.4326 76.0205 15.2695 76.0205 15.1047C76.0205 14.9399 76.0542 14.7769 76.1194 14.6255C76.1847 14.4742 76.2802 14.3378 76.4 14.2247C76.6671 13.9991 77.0054 13.8754 77.355 13.8754C77.7046 13.8754 78.0429 13.9991 78.31 14.2247C78.4299 14.3378 78.5254 14.4742 78.5906 14.6255C78.6559 14.7769 78.6895 14.9399 78.6895 15.1047C78.6895 15.2695 78.6559 15.4326 78.5906 15.5839C78.5254 15.7352 78.4299 15.8716 78.31 15.9847ZM78.52 25.2047C77.9256 25.2339 77.3383 25.0651 76.85 24.7247C76.6497 24.5717 76.4888 24.3729 76.381 24.145C76.2731 23.9171 76.2213 23.6667 76.23 23.4147V17.9747C76.2252 17.9355 76.2293 17.8956 76.2422 17.8582C76.255 17.8208 76.2762 17.7869 76.3042 17.7589C76.3322 17.7309 76.3661 17.7097 76.4035 17.6969C76.4409 17.684 76.4808 17.6799 76.52 17.6847H78.2C78.39 17.6847 78.48 17.7847 78.48 17.9747V22.6947C78.48 23.0747 78.65 23.2647 78.99 23.2647C79.1417 23.2702 79.2933 23.2533 79.44 23.2147C79.64 23.2147 79.75 23.2747 79.76 23.4547L79.91 24.7047C79.9172 24.7412 79.9165 24.7787 79.908 24.8149C79.8995 24.851 79.8833 24.885 79.8605 24.9143C79.8378 24.9437 79.809 24.9679 79.7762 24.9852C79.7433 25.0025 79.7071 25.0126 79.67 25.0147C79.2988 25.137 78.9109 25.2011 78.52 25.2047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M86.09 17.4447C86.6148 17.424 87.1383 17.5089 87.6296 17.6944C88.1209 17.88 88.57 18.1623 88.95 18.5247C89.6572 19.2837 90.0504 20.2824 90.0504 21.3197C90.0504 22.357 89.6572 23.3558 88.95 24.1147C88.5718 24.4804 88.1233 24.7655 87.6317 24.9528C87.1401 25.1402 86.6157 25.2259 86.09 25.2047C85.3412 25.2214 84.6073 24.9932 84 24.5547V28.1647C84 28.3547 83.9 28.4447 83.71 28.4447H82.03C81.9917 28.4519 81.9522 28.4496 81.9149 28.4381C81.8777 28.4265 81.8438 28.4061 81.8162 28.3785C81.7887 28.3509 81.7682 28.3171 81.7567 28.2798C81.7451 28.2426 81.7429 28.2031 81.75 28.1647V19.9647C81.7618 19.8845 81.7546 19.8027 81.7292 19.7257C81.7037 19.6488 81.6605 19.5788 81.6032 19.5215C81.5459 19.4642 81.476 19.4211 81.399 19.3956C81.3221 19.3701 81.2402 19.363 81.16 19.3747H80.83C80.61 19.3747 80.5 19.2947 80.5 19.1347V17.9547C80.4948 17.8817 80.5148 17.8091 80.5567 17.7491C80.5985 17.689 80.6597 17.6451 80.73 17.6247C81.0759 17.499 81.442 17.438 81.81 17.4447C82.177 17.4122 82.5453 17.4901 82.8678 17.6682C83.1902 17.8464 83.4522 18.1168 83.62 18.4447C83.9421 18.1189 84.3273 17.8622 84.752 17.6902C85.1767 17.5183 85.632 17.4347 86.09 17.4447ZM84.53 22.8147C84.7083 23.0011 84.9225 23.1494 85.1597 23.2507C85.3969 23.352 85.6521 23.4042 85.91 23.4042C86.1679 23.4042 86.4232 23.352 86.6603 23.2507C86.8975 23.1494 87.1117 23.0011 87.29 22.8147C87.6656 22.3958 87.8629 21.8469 87.84 21.2847C87.8662 20.7221 87.6684 20.1719 87.29 19.7547C87.1117 19.5684 86.8975 19.4201 86.6603 19.3188C86.4232 19.2174 86.1679 19.1652 85.91 19.1652C85.6521 19.1652 85.3969 19.2174 85.1597 19.3188C84.9225 19.4201 84.7083 19.5684 84.53 19.7547C84.1662 20.1793 83.9768 20.726 84 21.2847C83.9797 21.843 84.1688 22.3887 84.53 22.8147Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M94.77 25.2047C93.8723 25.2416 92.9822 25.0269 92.2 24.5847C91.8862 24.3957 91.619 24.1384 91.4181 23.832C91.2173 23.5256 91.0881 23.1779 91.04 22.8147C91.04 22.6147 91.11 22.5147 91.33 22.5147H92.8C92.8699 22.5175 92.9378 22.5394 92.996 22.5783C93.0542 22.6171 93.1006 22.6712 93.13 22.7347C93.34 23.2747 93.89 23.5447 94.77 23.5447C95.077 23.5588 95.3826 23.4969 95.66 23.3647C95.7558 23.3215 95.8379 23.2531 95.8978 23.1668C95.9577 23.0805 95.993 22.9795 96 22.8747C96 22.6147 95.84 22.4347 95.52 22.3147C95.1405 22.1884 94.7481 22.1045 94.35 22.0647C93.8785 22.0113 93.4109 21.9278 92.95 21.8147C92.5018 21.7133 92.0943 21.4799 91.78 21.1447C91.5949 20.9169 91.4587 20.6534 91.3797 20.3707C91.3008 20.088 91.2809 19.792 91.3212 19.5013C91.3616 19.2105 91.4613 18.9311 91.6142 18.6806C91.7671 18.43 91.9699 18.2136 92.21 18.0447C92.9308 17.5856 93.7765 17.3619 94.63 17.4047C95.4564 17.3768 96.274 17.5812 96.99 17.9947C97.2786 18.1582 97.527 18.3839 97.7173 18.6555C97.9076 18.9271 98.0349 19.2377 98.09 19.5647C98.09 19.7647 98 19.8647 97.82 19.8647H96.34C96.2777 19.8684 96.2157 19.8532 96.1622 19.8211C96.1087 19.789 96.0661 19.7414 96.04 19.6847C95.9411 19.4479 95.7549 19.2581 95.52 19.1547C95.255 19.0161 94.959 18.9472 94.66 18.9547C94.3669 18.9388 94.0745 18.9973 93.81 19.1247C93.7168 19.1607 93.6366 19.2237 93.5795 19.3057C93.5225 19.3877 93.4913 19.4849 93.49 19.5847C93.4964 19.7215 93.5465 19.8526 93.6329 19.9588C93.7193 20.065 93.8374 20.1406 93.97 20.1747C94.354 20.3195 94.7533 20.4201 95.16 20.4747C95.6277 20.5363 96.0917 20.6231 96.55 20.7347C96.9982 20.8362 97.4057 21.0695 97.72 21.4047C97.8882 21.5894 98.018 21.8055 98.1021 22.0407C98.1862 22.2758 98.2229 22.5253 98.21 22.7747C98.2186 23.1204 98.1375 23.4624 97.9745 23.7674C97.8115 24.0723 97.5722 24.3298 97.28 24.5147C96.5329 24.9944 95.6574 25.235 94.77 25.2047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M108.78 24.7047C108.786 24.7402 108.784 24.7765 108.776 24.8114C108.767 24.8464 108.752 24.8792 108.73 24.9081C108.709 24.937 108.682 24.9613 108.651 24.9796C108.62 24.9979 108.586 25.0098 108.55 25.0147C108.185 25.1339 107.804 25.198 107.42 25.2047C107.04 25.2441 106.656 25.1847 106.306 25.0323C105.955 24.8799 105.65 24.6396 105.42 24.3347C104.714 24.942 103.8 25.2536 102.87 25.2047C102.438 25.2246 102.007 25.1539 101.604 24.9972C101.201 24.8405 100.835 24.6012 100.53 24.2947C100.227 23.9736 99.9922 23.5946 99.8392 23.1805C99.6863 22.7664 99.6186 22.3257 99.64 21.8847V17.9747C99.64 17.7847 99.73 17.6847 99.92 17.6847H101.6C101.79 17.6847 101.88 17.7847 101.88 17.9747V21.5847C101.862 22.0345 102.015 22.4743 102.31 22.8147C102.457 22.9707 102.636 23.0933 102.834 23.1744C103.032 23.2555 103.246 23.2931 103.46 23.2847C103.679 23.2943 103.898 23.2604 104.104 23.1848C104.31 23.1093 104.499 22.9937 104.66 22.8447C104.812 22.6877 104.931 22.5011 105.008 22.2964C105.086 22.0917 105.12 21.8733 105.11 21.6547V17.9747C105.11 17.7847 105.2 17.6847 105.39 17.6847H107.09C107.28 17.6847 107.37 17.7847 107.37 17.9747V22.6847C107.37 23.0747 107.54 23.2647 107.87 23.2647C108.025 23.2707 108.18 23.2539 108.33 23.2147C108.368 23.2041 108.408 23.2022 108.446 23.2092C108.485 23.2161 108.521 23.2317 108.553 23.2548C108.585 23.2779 108.611 23.3079 108.63 23.3425C108.648 23.3771 108.658 23.4155 108.66 23.4547L108.78 24.7047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M124.67 24.7047C124.679 24.7405 124.68 24.7779 124.673 24.8141C124.665 24.8502 124.65 24.8844 124.628 24.914C124.606 24.9436 124.578 24.968 124.545 24.9854C124.513 25.0029 124.477 25.0129 124.44 25.0147C124.068 25.1356 123.681 25.1997 123.29 25.2047C122.695 25.2354 122.108 25.0665 121.62 24.7247C121.409 24.5783 121.238 24.3822 121.121 24.1537C121.004 23.9252 120.945 23.6713 120.95 23.4147V21.0647C120.971 20.6163 120.821 20.1766 120.53 19.8347C120.39 19.6784 120.216 19.5552 120.023 19.4739C119.829 19.3927 119.62 19.3554 119.41 19.3647C119.221 19.3576 119.033 19.3935 118.859 19.4697C118.686 19.5459 118.533 19.6605 118.41 19.8047C118.146 20.1398 118.011 20.5586 118.03 20.9847V24.6747C118.03 24.8647 117.94 24.9647 117.75 24.9647H116.06C116.021 24.9696 115.981 24.9654 115.944 24.9526C115.906 24.9397 115.872 24.9185 115.844 24.8905C115.816 24.8626 115.795 24.8286 115.782 24.7912C115.769 24.7538 115.765 24.714 115.77 24.6747V21.0647C115.792 20.6212 115.653 20.1846 115.38 19.8347C115.258 19.6877 115.105 19.5694 114.932 19.4882C114.76 19.407 114.571 19.3648 114.38 19.3647C114.176 19.3565 113.973 19.3914 113.783 19.4673C113.593 19.5431 113.422 19.6581 113.28 19.8047C112.994 20.1291 112.847 20.5529 112.87 20.9847V24.6747C112.875 24.714 112.871 24.7538 112.858 24.7912C112.845 24.8286 112.824 24.8626 112.796 24.8905C112.768 24.9185 112.734 24.9397 112.697 24.9526C112.659 24.9654 112.619 24.9696 112.58 24.9647H110.95C110.76 24.9647 110.67 24.8647 110.67 24.6747V19.9647C110.682 19.8845 110.675 19.8027 110.649 19.7257C110.624 19.6488 110.581 19.5788 110.523 19.5215C110.466 19.4642 110.396 19.4211 110.319 19.3956C110.242 19.3701 110.16 19.363 110.08 19.3747H109.75C109.53 19.3747 109.42 19.2947 109.42 19.1347V17.9547C109.415 17.8817 109.435 17.8091 109.477 17.7491C109.519 17.689 109.58 17.6451 109.65 17.6247C109.996 17.499 110.362 17.438 110.73 17.4447C111.083 17.4146 111.438 17.485 111.753 17.6478C112.068 17.8106 112.33 18.0591 112.51 18.3647C112.847 18.045 113.247 17.7982 113.684 17.6399C114.121 17.4816 114.586 17.4152 115.05 17.4447C115.501 17.4227 115.95 17.5072 116.362 17.6914C116.774 17.8756 117.136 18.1542 117.42 18.5047C117.751 18.145 118.158 17.8634 118.611 17.68C119.064 17.4967 119.552 17.4164 120.04 17.4447C120.476 17.4243 120.912 17.4946 121.32 17.6513C121.728 17.8079 122.099 18.0474 122.41 18.3547C122.714 18.6752 122.949 19.0541 123.102 19.4684C123.255 19.8826 123.323 20.3237 123.3 20.7647V22.6947C123.3 23.0747 123.47 23.2647 123.79 23.2647C123.945 23.2719 124.1 23.2551 124.25 23.2147C124.457 23.2147 124.567 23.2947 124.58 23.4547L124.67 24.7047Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M7.41 16.3847C8.14777 13.4194 9.85643 10.7861 12.2639 8.90424C14.6714 7.02234 17.6393 6 20.695 6C23.7507 6 26.7186 7.02234 29.1261 8.90424C31.5336 10.7861 33.2422 13.4194 33.98 16.3847H32.78C30.7557 16.3549 28.7729 16.9599 27.11 18.1147C27.014 18.1842 26.9138 18.2477 26.81 18.3047H26.67C26.5662 18.2477 26.466 18.1842 26.37 18.1147C24.6924 16.9866 22.7166 16.3841 20.695 16.3841C18.6734 16.3841 16.6976 16.9866 15.02 18.1147C14.924 18.1842 14.8238 18.2477 14.72 18.3047H14.58C14.4762 18.2477 14.376 18.1842 14.28 18.1147C12.6171 16.9599 10.6343 16.3549 8.61 16.3847H7.41ZM30.62 22.6547C31.236 22.175 31.9995 21.924 32.78 21.9447H34.39V18.7347H32.78C31.4052 18.7181 30.0619 19.146 28.95 19.9547C28.3243 20.416 27.5674 20.6649 26.79 20.6649C26.0126 20.6649 25.2557 20.416 24.63 19.9547C23.4899 19.1611 22.1341 18.7356 20.745 18.7356C19.3559 18.7356 18.0001 19.1611 16.86 19.9547C16.2343 20.416 15.4774 20.6649 14.7 20.6649C13.9226 20.6649 13.1657 20.416 12.54 19.9547C11.4144 19.1356 10.0518 18.7072 8.66 18.7347H7V21.9447H8.61C9.39051 21.924 10.154 22.175 10.77 22.6547C11.908 23.4489 13.2623 23.8747 14.65 23.8747C16.0377 23.8747 17.392 23.4489 18.53 22.6547C19.1468 22.1765 19.9097 21.9257 20.69 21.9447C21.4708 21.9223 22.2348 22.1735 22.85 22.6547C23.9901 23.4484 25.3459 23.8738 26.735 23.8738C28.1241 23.8738 29.4799 23.4484 30.62 22.6547V22.6547ZM30.62 28.3947C31.236 27.915 31.9995 27.664 32.78 27.6847H34.39V24.4747H32.78C31.4052 24.4581 30.0619 24.886 28.95 25.6947C28.3243 26.156 27.5674 26.4049 26.79 26.4049C26.0126 26.4049 25.2557 26.156 24.63 25.6947C23.4899 24.9011 22.1341 24.4757 20.745 24.4757C19.3559 24.4757 18.0001 24.9011 16.86 25.6947C16.2343 26.156 15.4774 26.4049 14.7 26.4049C13.9226 26.4049 13.1657 26.156 12.54 25.6947C11.4144 24.8757 10.0518 24.4472 8.66 24.4747H7V27.6847H8.61C9.39051 27.664 10.154 27.915 10.77 28.3947C11.908 29.1889 13.2623 29.6147 14.65 29.6147C16.0377 29.6147 17.392 29.1889 18.53 28.3947C19.1468 27.9165 19.9097 27.6657 20.69 27.6847C21.4708 27.6623 22.2348 27.9135 22.85 28.3947C23.9901 29.1884 25.3459 29.6138 26.735 29.6138C28.1241 29.6138 29.4799 29.1884 30.62 28.3947V28.3947Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-53' width='169' height='42' viewBox='0 0 169 42' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M50.8601 29.3532H62.8121V25.7532H55.1081V12.1932H50.8601V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M69.8932 26.9532C68.1892 26.9532 67.3012 25.4652 67.3012 23.2332C67.3012 21.0012 68.1892 19.4892 69.8932 19.4892C71.5972 19.4892 72.5092 21.0012 72.5092 23.2332C72.5092 25.4652 71.5972 26.9532 69.8932 26.9532ZM69.9172 29.7372C73.8772 29.7372 76.4692 26.9292 76.4692 23.2332C76.4692 19.5372 73.8772 16.7292 69.9172 16.7292C65.9812 16.7292 63.3412 19.5372 63.3412 23.2332C63.3412 26.9292 65.9812 29.7372 69.9172 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M83.3237 33.6012C85.1477 33.6012 86.7557 33.1932 87.8357 32.2332C88.8197 31.3452 89.4677 30.0012 89.4677 28.1532V17.0652H85.7237V18.3852H85.6757C84.9557 17.3532 83.8517 16.7052 82.2197 16.7052C79.1717 16.7052 77.0597 19.2492 77.0597 22.8492C77.0597 26.6172 79.6277 28.6812 82.3877 28.6812C83.8757 28.6812 84.8117 28.0812 85.5317 27.2652H85.6277V28.4892C85.6277 29.9772 84.9317 30.8412 83.2757 30.8412C81.9797 30.8412 81.3317 30.2892 81.1157 29.6412H77.3237C77.7077 32.2092 79.9397 33.6012 83.3237 33.6012ZM83.2997 25.7772C81.8357 25.7772 80.8757 24.5772 80.8757 22.7292C80.8757 20.8572 81.8357 19.6572 83.2997 19.6572C84.9317 19.6572 85.7957 21.0492 85.7957 22.7052C85.7957 24.4332 85.0037 25.7772 83.2997 25.7772Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M97.166 26.9532C95.462 26.9532 94.574 25.4652 94.574 23.2332C94.574 21.0012 95.462 19.4892 97.166 19.4892C98.87 19.4892 99.782 21.0012 99.782 23.2332C99.782 25.4652 98.87 26.9532 97.166 26.9532ZM97.19 29.7372C101.15 29.7372 103.742 26.9292 103.742 23.2332C103.742 19.5372 101.15 16.7292 97.19 16.7292C93.254 16.7292 90.614 19.5372 90.614 23.2332C90.614 26.9292 93.254 29.7372 97.19 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M104.884 29.3532H108.796V17.0652H104.884V29.3532ZM104.884 15.3612H108.796V12.1932H104.884V15.3612Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M110.494 33.4092H114.406V28.0812H114.454C115.222 29.1132 116.35 29.7372 117.934 29.7372C121.15 29.7372 123.286 27.1932 123.286 23.2092C123.286 19.5132 121.294 16.7052 118.03 16.7052C116.35 16.7052 115.15 17.4492 114.31 18.5532H114.238V17.0652H110.494V33.4092ZM116.926 26.7132C115.246 26.7132 114.286 25.3452 114.286 23.3532C114.286 21.3612 115.15 19.8492 116.854 19.8492C118.534 19.8492 119.326 21.2412 119.326 23.3532C119.326 25.4412 118.414 26.7132 116.926 26.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M129.655 29.7372C132.871 29.7372 135.247 28.3452 135.247 25.6572C135.247 22.5132 132.703 21.9612 130.543 21.6012C128.983 21.3132 127.591 21.1932 127.591 20.3292C127.591 19.5612 128.335 19.2012 129.295 19.2012C130.375 19.2012 131.119 19.5372 131.263 20.6412H134.863C134.671 18.2172 132.799 16.7052 129.319 16.7052C126.415 16.7052 124.015 18.0492 124.015 20.6412C124.015 23.5212 126.295 24.0972 128.431 24.4572C130.063 24.7452 131.551 24.8652 131.551 25.9692C131.551 26.7612 130.807 27.1932 129.631 27.1932C128.335 27.1932 127.519 26.5932 127.375 25.3692H123.679C123.799 28.0812 126.055 29.7372 129.655 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M140.561 29.7132C142.265 29.7132 143.345 29.0412 144.233 27.8412H144.305V29.3532H148.049V17.0652H144.137V23.9292C144.137 25.3932 143.321 26.4012 141.977 26.4012C140.729 26.4012 140.129 25.6572 140.129 24.3132V17.0652H136.241V25.1292C136.241 27.8652 137.729 29.7132 140.561 29.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M149.75 29.3532H153.662V22.4652C153.662 21.0012 154.382 19.9692 155.606 19.9692C156.782 19.9692 157.334 20.7372 157.334 22.0572V29.3532H161.246V22.4652C161.246 21.0012 161.942 19.9692 163.19 19.9692C164.366 19.9692 164.918 20.7372 164.918 22.0572V29.3532H168.83V21.3612C168.83 18.6012 167.438 16.7052 164.654 16.7052C163.07 16.7052 161.75 17.3772 160.79 18.8652H160.742C160.118 17.5452 158.894 16.7052 157.286 16.7052C155.51 16.7052 154.334 17.5452 153.566 18.8172H153.494V17.0652H149.75V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath fill-rule='evenodd' clip-rule='evenodd' d='M20.6842 0.961929C31.946 0.961929 41.0755 10.0914 41.0755 21.3532C41.0755 32.6151 31.946 41.7446 20.6842 41.7446C9.42234 41.7446 0.292847 32.6151 0.292847 21.3532C0.292847 10.0914 9.42234 0.961929 20.6842 0.961929ZM40.2928 21.3532C40.2928 10.5237 31.5137 1.74455 20.6842 1.74455C19.8106 1.74455 18.9505 1.80167 18.1071 1.91238C18.652 1.86474 19.2034 1.84042 19.7606 1.84042C30.1088 1.84042 38.4977 10.2293 38.4977 20.5775C38.4977 30.9256 30.1088 39.3145 19.7606 39.3145C9.96366 39.3145 1.92284 31.7956 1.09401 22.2135C1.54426 32.6439 10.1428 40.9619 20.6842 40.9619C31.5137 40.9619 40.2928 32.1828 40.2928 21.3532ZM37.715 20.5775C37.715 10.6615 29.6766 2.62305 19.7606 2.62305C18.9555 2.62305 18.1627 2.67605 17.3856 2.77874C17.8641 2.73848 18.3482 2.71794 18.8371 2.71794C28.2717 2.71794 35.9199 10.3662 35.9199 19.8007C35.9199 29.2353 28.2717 36.8835 18.8371 36.8835C9.91648 36.8835 2.59287 30.0458 1.8215 21.3256C2.21369 30.8946 10.0953 38.5319 19.7606 38.5319C29.6766 38.5319 37.715 30.4934 37.715 20.5775ZM18.8371 3.50057C27.8394 3.50057 35.1373 10.7984 35.1373 19.8007C35.1373 28.803 27.8394 36.1008 18.8371 36.1008C10.0434 36.1008 2.87602 29.1372 2.54867 20.4235C3.25542 28.2885 9.86471 34.4524 17.9137 34.4524C26.434 34.4524 33.3412 27.5453 33.3412 19.0249C33.3412 10.5045 26.434 3.59741 17.9137 3.59741C17.4729 3.59741 17.0364 3.6159 16.605 3.65213C17.3348 3.5522 18.0799 3.50057 18.8371 3.50057ZM32.5585 19.0249C32.5585 10.9368 26.0018 4.38004 17.9137 4.38004C17.2303 4.38004 16.5578 4.42684 15.8994 4.51742C16.2589 4.48928 16.6223 4.47495 16.9891 4.47495C24.5959 4.47495 30.7624 10.6414 30.7624 18.2482C30.7624 25.8549 24.5959 32.0214 16.9891 32.0214C9.82947 32.0214 3.94576 26.5585 3.27885 19.5736C3.56738 27.4075 10.0092 33.6698 17.9137 33.6698C26.0018 33.6698 32.5585 27.1131 32.5585 19.0249ZM16.9891 5.25757C24.1636 5.25757 29.9797 11.0737 29.9797 18.2482C29.9797 25.4227 24.1636 31.2388 16.9891 31.2388C9.95594 31.2388 4.2282 25.6496 4.00526 18.6706C4.60739 24.8008 9.77718 29.5904 16.0656 29.5904C22.7588 29.5904 28.1846 24.1645 28.1846 17.4714C28.1846 10.7783 22.7588 5.35246 16.0656 5.35246C15.7587 5.35246 15.4544 5.36387 15.1532 5.38629C15.753 5.30145 16.3659 5.25757 16.9891 5.25757ZM27.402 17.4714C27.402 11.2105 22.3265 6.13509 16.0656 6.13509C15.4941 6.13509 14.9325 6.17738 14.3837 6.259C14.6342 6.24106 14.8871 6.23193 15.1422 6.23193C20.9211 6.23193 25.6059 10.9167 25.6059 16.6956C25.6059 22.4746 20.9211 27.1593 15.1422 27.1593C9.72697 27.1593 5.27257 23.0458 4.73324 17.773C4.89313 23.8945 9.90561 28.8078 16.0656 28.8078C22.3265 28.8078 27.402 23.7323 27.402 17.4714ZM15.1422 7.01456C20.4889 7.01456 24.8232 11.3489 24.8232 16.6956C24.8232 22.0424 20.4889 26.3767 15.1422 26.3767C9.86348 26.3767 5.57156 22.152 5.46317 16.8993C5.9508 21.3032 9.68475 24.7283 14.2187 24.7283C19.084 24.7283 23.0281 20.7842 23.0281 15.9189C23.0281 11.0536 19.084 7.10945 14.2187 7.10945C14.0326 7.10945 13.8479 7.11522 13.6647 7.12659C14.1464 7.05282 14.6398 7.01456 15.1422 7.01456ZM22.2455 15.9189C22.2455 11.4858 18.6518 7.89208 14.2187 7.89208C13.7735 7.89208 13.3368 7.92832 12.9113 7.99801C13.0381 7.99133 13.1657 7.98795 13.2942 7.98795C17.2458 7.98795 20.4493 11.1914 20.4493 15.1431C20.4493 19.0948 17.2458 22.2983 13.2942 22.2983C9.64023 22.2983 6.626 19.5593 6.19252 16.0225C6.24802 20.4079 9.8202 23.9457 14.2187 23.9457C18.6518 23.9457 22.2455 20.352 22.2455 15.9189ZM13.2942 8.77057C16.8136 8.77057 19.6667 11.6236 19.6667 15.1431C19.6667 18.6626 16.8136 21.5156 13.2942 21.5156C9.77471 21.5156 6.92163 18.6626 6.92163 15.1431C6.92163 15.1347 6.92165 15.1262 6.92168 15.1178C7.2881 17.7998 9.58806 19.8663 12.3707 19.8663C15.4082 19.8663 17.8706 17.4039 17.8706 14.3664C17.8706 11.3288 15.4082 8.86646 12.3707 8.86646C12.302 8.86646 12.2336 8.86771 12.1655 8.87021C12.5318 8.80474 12.909 8.77057 13.2942 8.77057ZM17.0879 14.3664C17.0879 11.7611 14.976 9.64908 12.3707 9.64908C9.7654 9.64908 7.6534 11.7611 7.6534 14.3664C7.6534 16.9716 9.7654 19.0836 12.3707 19.0836C14.976 19.0836 17.0879 16.9716 17.0879 14.3664Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-53' width='169' height='42' viewBox='0 0 169 42' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M50.8601 29.3532H62.8121V25.7532H55.1081V12.1932H50.8601V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M69.8932 26.9532C68.1892 26.9532 67.3012 25.4652 67.3012 23.2332C67.3012 21.0012 68.1892 19.4892 69.8932 19.4892C71.5972 19.4892 72.5092 21.0012 72.5092 23.2332C72.5092 25.4652 71.5972 26.9532 69.8932 26.9532ZM69.9172 29.7372C73.8772 29.7372 76.4692 26.9292 76.4692 23.2332C76.4692 19.5372 73.8772 16.7292 69.9172 16.7292C65.9812 16.7292 63.3412 19.5372 63.3412 23.2332C63.3412 26.9292 65.9812 29.7372 69.9172 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M83.3237 33.6012C85.1477 33.6012 86.7557 33.1932 87.8357 32.2332C88.8197 31.3452 89.4677 30.0012 89.4677 28.1532V17.0652H85.7237V18.3852H85.6757C84.9557 17.3532 83.8517 16.7052 82.2197 16.7052C79.1717 16.7052 77.0597 19.2492 77.0597 22.8492C77.0597 26.6172 79.6277 28.6812 82.3877 28.6812C83.8757 28.6812 84.8117 28.0812 85.5317 27.2652H85.6277V28.4892C85.6277 29.9772 84.9317 30.8412 83.2757 30.8412C81.9797 30.8412 81.3317 30.2892 81.1157 29.6412H77.3237C77.7077 32.2092 79.9397 33.6012 83.3237 33.6012ZM83.2997 25.7772C81.8357 25.7772 80.8757 24.5772 80.8757 22.7292C80.8757 20.8572 81.8357 19.6572 83.2997 19.6572C84.9317 19.6572 85.7957 21.0492 85.7957 22.7052C85.7957 24.4332 85.0037 25.7772 83.2997 25.7772Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M97.166 26.9532C95.462 26.9532 94.574 25.4652 94.574 23.2332C94.574 21.0012 95.462 19.4892 97.166 19.4892C98.87 19.4892 99.782 21.0012 99.782 23.2332C99.782 25.4652 98.87 26.9532 97.166 26.9532ZM97.19 29.7372C101.15 29.7372 103.742 26.9292 103.742 23.2332C103.742 19.5372 101.15 16.7292 97.19 16.7292C93.254 16.7292 90.614 19.5372 90.614 23.2332C90.614 26.9292 93.254 29.7372 97.19 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M104.884 29.3532H108.796V17.0652H104.884V29.3532ZM104.884 15.3612H108.796V12.1932H104.884V15.3612Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M110.494 33.4092H114.406V28.0812H114.454C115.222 29.1132 116.35 29.7372 117.934 29.7372C121.15 29.7372 123.286 27.1932 123.286 23.2092C123.286 19.5132 121.294 16.7052 118.03 16.7052C116.35 16.7052 115.15 17.4492 114.31 18.5532H114.238V17.0652H110.494V33.4092ZM116.926 26.7132C115.246 26.7132 114.286 25.3452 114.286 23.3532C114.286 21.3612 115.15 19.8492 116.854 19.8492C118.534 19.8492 119.326 21.2412 119.326 23.3532C119.326 25.4412 118.414 26.7132 116.926 26.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M129.655 29.7372C132.871 29.7372 135.247 28.3452 135.247 25.6572C135.247 22.5132 132.703 21.9612 130.543 21.6012C128.983 21.3132 127.591 21.1932 127.591 20.3292C127.591 19.5612 128.335 19.2012 129.295 19.2012C130.375 19.2012 131.119 19.5372 131.263 20.6412H134.863C134.671 18.2172 132.799 16.7052 129.319 16.7052C126.415 16.7052 124.015 18.0492 124.015 20.6412C124.015 23.5212 126.295 24.0972 128.431 24.4572C130.063 24.7452 131.551 24.8652 131.551 25.9692C131.551 26.7612 130.807 27.1932 129.631 27.1932C128.335 27.1932 127.519 26.5932 127.375 25.3692H123.679C123.799 28.0812 126.055 29.7372 129.655 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M140.561 29.7132C142.265 29.7132 143.345 29.0412 144.233 27.8412H144.305V29.3532H148.049V17.0652H144.137V23.9292C144.137 25.3932 143.321 26.4012 141.977 26.4012C140.729 26.4012 140.129 25.6572 140.129 24.3132V17.0652H136.241V25.1292C136.241 27.8652 137.729 29.7132 140.561 29.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M149.75 29.3532H153.662V22.4652C153.662 21.0012 154.382 19.9692 155.606 19.9692C156.782 19.9692 157.334 20.7372 157.334 22.0572V29.3532H161.246V22.4652C161.246 21.0012 161.942 19.9692 163.19 19.9692C164.366 19.9692 164.918 20.7372 164.918 22.0572V29.3532H168.83V21.3612C168.83 18.6012 167.438 16.7052 164.654 16.7052C163.07 16.7052 161.75 17.3772 160.79 18.8652H160.742C160.118 17.5452 158.894 16.7052 157.286 16.7052C155.51 16.7052 154.334 17.5452 153.566 18.8172H153.494V17.0652H149.75V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath fill-rule='evenodd' clip-rule='evenodd' d='M20.6842 0.961929C31.946 0.961929 41.0755 10.0914 41.0755 21.3532C41.0755 32.6151 31.946 41.7446 20.6842 41.7446C9.42234 41.7446 0.292847 32.6151 0.292847 21.3532C0.292847 10.0914 9.42234 0.961929 20.6842 0.961929ZM40.2928 21.3532C40.2928 10.5237 31.5137 1.74455 20.6842 1.74455C19.8106 1.74455 18.9505 1.80167 18.1071 1.91238C18.652 1.86474 19.2034 1.84042 19.7606 1.84042C30.1088 1.84042 38.4977 10.2293 38.4977 20.5775C38.4977 30.9256 30.1088 39.3145 19.7606 39.3145C9.96366 39.3145 1.92284 31.7956 1.09401 22.2135C1.54426 32.6439 10.1428 40.9619 20.6842 40.9619C31.5137 40.9619 40.2928 32.1828 40.2928 21.3532ZM37.715 20.5775C37.715 10.6615 29.6766 2.62305 19.7606 2.62305C18.9555 2.62305 18.1627 2.67605 17.3856 2.77874C17.8641 2.73848 18.3482 2.71794 18.8371 2.71794C28.2717 2.71794 35.9199 10.3662 35.9199 19.8007C35.9199 29.2353 28.2717 36.8835 18.8371 36.8835C9.91648 36.8835 2.59287 30.0458 1.8215 21.3256C2.21369 30.8946 10.0953 38.5319 19.7606 38.5319C29.6766 38.5319 37.715 30.4934 37.715 20.5775ZM18.8371 3.50057C27.8394 3.50057 35.1373 10.7984 35.1373 19.8007C35.1373 28.803 27.8394 36.1008 18.8371 36.1008C10.0434 36.1008 2.87602 29.1372 2.54867 20.4235C3.25542 28.2885 9.86471 34.4524 17.9137 34.4524C26.434 34.4524 33.3412 27.5453 33.3412 19.0249C33.3412 10.5045 26.434 3.59741 17.9137 3.59741C17.4729 3.59741 17.0364 3.6159 16.605 3.65213C17.3348 3.5522 18.0799 3.50057 18.8371 3.50057ZM32.5585 19.0249C32.5585 10.9368 26.0018 4.38004 17.9137 4.38004C17.2303 4.38004 16.5578 4.42684 15.8994 4.51742C16.2589 4.48928 16.6223 4.47495 16.9891 4.47495C24.5959 4.47495 30.7624 10.6414 30.7624 18.2482C30.7624 25.8549 24.5959 32.0214 16.9891 32.0214C9.82947 32.0214 3.94576 26.5585 3.27885 19.5736C3.56738 27.4075 10.0092 33.6698 17.9137 33.6698C26.0018 33.6698 32.5585 27.1131 32.5585 19.0249ZM16.9891 5.25757C24.1636 5.25757 29.9797 11.0737 29.9797 18.2482C29.9797 25.4227 24.1636 31.2388 16.9891 31.2388C9.95594 31.2388 4.2282 25.6496 4.00526 18.6706C4.60739 24.8008 9.77718 29.5904 16.0656 29.5904C22.7588 29.5904 28.1846 24.1645 28.1846 17.4714C28.1846 10.7783 22.7588 5.35246 16.0656 5.35246C15.7587 5.35246 15.4544 5.36387 15.1532 5.38629C15.753 5.30145 16.3659 5.25757 16.9891 5.25757ZM27.402 17.4714C27.402 11.2105 22.3265 6.13509 16.0656 6.13509C15.4941 6.13509 14.9325 6.17738 14.3837 6.259C14.6342 6.24106 14.8871 6.23193 15.1422 6.23193C20.9211 6.23193 25.6059 10.9167 25.6059 16.6956C25.6059 22.4746 20.9211 27.1593 15.1422 27.1593C9.72697 27.1593 5.27257 23.0458 4.73324 17.773C4.89313 23.8945 9.90561 28.8078 16.0656 28.8078C22.3265 28.8078 27.402 23.7323 27.402 17.4714ZM15.1422 7.01456C20.4889 7.01456 24.8232 11.3489 24.8232 16.6956C24.8232 22.0424 20.4889 26.3767 15.1422 26.3767C9.86348 26.3767 5.57156 22.152 5.46317 16.8993C5.9508 21.3032 9.68475 24.7283 14.2187 24.7283C19.084 24.7283 23.0281 20.7842 23.0281 15.9189C23.0281 11.0536 19.084 7.10945 14.2187 7.10945C14.0326 7.10945 13.8479 7.11522 13.6647 7.12659C14.1464 7.05282 14.6398 7.01456 15.1422 7.01456ZM22.2455 15.9189C22.2455 11.4858 18.6518 7.89208 14.2187 7.89208C13.7735 7.89208 13.3368 7.92832 12.9113 7.99801C13.0381 7.99133 13.1657 7.98795 13.2942 7.98795C17.2458 7.98795 20.4493 11.1914 20.4493 15.1431C20.4493 19.0948 17.2458 22.2983 13.2942 22.2983C9.64023 22.2983 6.626 19.5593 6.19252 16.0225C6.24802 20.4079 9.8202 23.9457 14.2187 23.9457C18.6518 23.9457 22.2455 20.352 22.2455 15.9189ZM13.2942 8.77057C16.8136 8.77057 19.6667 11.6236 19.6667 15.1431C19.6667 18.6626 16.8136 21.5156 13.2942 21.5156C9.77471 21.5156 6.92163 18.6626 6.92163 15.1431C6.92163 15.1347 6.92165 15.1262 6.92168 15.1178C7.2881 17.7998 9.58806 19.8663 12.3707 19.8663C15.4082 19.8663 17.8706 17.4039 17.8706 14.3664C17.8706 11.3288 15.4082 8.86646 12.3707 8.86646C12.302 8.86646 12.2336 8.86771 12.1655 8.87021C12.5318 8.80474 12.909 8.77057 13.2942 8.77057ZM17.0879 14.3664C17.0879 11.7611 14.976 9.64908 12.3707 9.64908C9.7654 9.64908 7.6534 11.7611 7.6534 14.3664C7.6534 16.9716 9.7654 19.0836 12.3707 19.0836C14.976 19.0836 17.0879 16.9716 17.0879 14.3664Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-55' width='168' height='41' viewBox='0 0 168 41' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M49.2775 28.9524H61.2295V25.3524H53.5255V11.7924H49.2775V28.9524Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M68.3107 26.5524C66.6067 26.5524 65.7187 25.0644 65.7187 22.8324C65.7187 20.6004 66.6067 19.0884 68.3107 19.0884C70.0147 19.0884 70.9267 20.6004 70.9267 22.8324C70.9267 25.0644 70.0147 26.5524 68.3107 26.5524ZM68.3347 29.3364C72.2947 29.3364 74.8867 26.5284 74.8867 22.8324C74.8867 19.1364 72.2947 16.3284 68.3347 16.3284C64.3987 16.3284 61.7587 19.1364 61.7587 22.8324C61.7587 26.5284 64.3987 29.3364 68.3347 29.3364Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M81.7411 33.2004C83.5651 33.2004 85.1731 32.7924 86.2531 31.8324C87.2371 30.9444 87.8851 29.6004 87.8851 27.7524V16.6644H84.1411V17.9844H84.0931C83.3731 16.9524 82.2691 16.3044 80.6371 16.3044C77.5891 16.3044 75.4771 18.8484 75.4771 22.4484C75.4771 26.2164 78.0451 28.2804 80.8051 28.2804C82.2931 28.2804 83.2291 27.6804 83.9491 26.8644H84.0451V28.0884C84.0451 29.5764 83.3491 30.4404 81.6931 30.4404C80.3971 30.4404 79.7491 29.8884 79.5331 29.2404H75.7411C76.1251 31.8084 78.3571 33.2004 81.7411 33.2004ZM81.7171 25.3764C80.2531 25.3764 79.2931 24.1764 79.2931 22.3284C79.2931 20.4564 80.2531 19.2564 81.7171 19.2564C83.3491 19.2564 84.2131 20.6484 84.2131 22.3044C84.2131 24.0324 83.4211 25.3764 81.7171 25.3764Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M95.5835 26.5524C93.8795 26.5524 92.9915 25.0644 92.9915 22.8324C92.9915 20.6004 93.8795 19.0884 95.5835 19.0884C97.2875 19.0884 98.1995 20.6004 98.1995 22.8324C98.1995 25.0644 97.2875 26.5524 95.5835 26.5524ZM95.6075 29.3364C99.5675 29.3364 102.159 26.5284 102.159 22.8324C102.159 19.1364 99.5675 16.3284 95.6075 16.3284C91.6715 16.3284 89.0315 19.1364 89.0315 22.8324C89.0315 26.5284 91.6715 29.3364 95.6075 29.3364Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M103.302 28.9524H107.214V16.6644H103.302V28.9524ZM103.302 14.9604H107.214V11.7924H103.302V14.9604Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M108.911 33.0084H112.823V27.6804H112.871C113.639 28.7124 114.767 29.3364 116.351 29.3364C119.567 29.3364 121.703 26.7924 121.703 22.8084C121.703 19.1124 119.711 16.3044 116.447 16.3044C114.767 16.3044 113.567 17.0484 112.727 18.1524H112.655V16.6644H108.911V33.0084ZM115.343 26.3124C113.663 26.3124 112.703 24.9444 112.703 22.9524C112.703 20.9604 113.567 19.4484 115.271 19.4484C116.951 19.4484 117.743 20.8404 117.743 22.9524C117.743 25.0404 116.831 26.3124 115.343 26.3124Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M128.072 29.3364C131.288 29.3364 133.664 27.9444 133.664 25.2564C133.664 22.1124 131.12 21.5604 128.96 21.2004C127.4 20.9124 126.008 20.7924 126.008 19.9284C126.008 19.1604 126.752 18.8004 127.712 18.8004C128.792 18.8004 129.536 19.1364 129.68 20.2404H133.28C133.088 17.8164 131.216 16.3044 127.736 16.3044C124.832 16.3044 122.432 17.6484 122.432 20.2404C122.432 23.1204 124.712 23.6964 126.848 24.0564C128.48 24.3444 129.968 24.4644 129.968 25.5684C129.968 26.3604 129.224 26.7924 128.048 26.7924C126.752 26.7924 125.936 26.1924 125.792 24.9684H122.096C122.216 27.6804 124.472 29.3364 128.072 29.3364Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M138.978 29.3124C140.682 29.3124 141.762 28.6404 142.65 27.4404H142.722V28.9524H146.466V16.6644H142.554V23.5284C142.554 24.9924 141.738 26.0004 140.394 26.0004C139.146 26.0004 138.546 25.2564 138.546 23.9124V16.6644H134.658V24.7284C134.658 27.4644 136.146 29.3124 138.978 29.3124Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M148.168 28.9524H152.08V22.0644C152.08 20.6004 152.8 19.5684 154.024 19.5684C155.2 19.5684 155.752 20.3364 155.752 21.6564V28.9524H159.664V22.0644C159.664 20.6004 160.36 19.5684 161.608 19.5684C162.784 19.5684 163.336 20.3364 163.336 21.6564V28.9524H167.248V20.9604C167.248 18.2004 165.856 16.3044 163.072 16.3044C161.488 16.3044 160.168 16.9764 159.208 18.4644H159.16C158.536 17.1444 157.312 16.3044 155.704 16.3044C153.928 16.3044 152.752 17.1444 151.984 18.4164H151.912V16.6644H148.168V28.9524Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M25.4099 1.97689L21.4769 0.923031L18.1625 13.2926L15.1702 2.12527L11.2371 3.17913L14.4701 15.2446L6.41746 7.19201L3.53827 10.0712L12.371 18.904L1.37124 15.9566L0.317383 19.8896L12.336 23.11C12.1984 22.5165 12.1256 21.8981 12.1256 21.2627C12.1256 16.7651 15.7716 13.1191 20.2692 13.1191C24.7668 13.1191 28.4128 16.7651 28.4128 21.2627C28.4128 21.894 28.3409 22.5086 28.205 23.0986L39.1277 26.0253L40.1815 22.0923L28.1151 18.8591L39.1156 15.9115L38.0617 11.9785L25.9958 15.2115L34.0484 7.15895L31.1692 4.27976L22.459 12.99L25.4099 1.97689Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3Cpath d='M28.1943 23.1444C27.8571 24.57 27.1452 25.8507 26.1684 26.8768L34.0814 34.7899L36.9606 31.9107L28.1943 23.1444Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3Cpath d='M26.0884 26.9596C25.0998 27.9693 23.8505 28.7228 22.4495 29.1111L25.3289 39.8571L29.2619 38.8032L26.0884 26.9596Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3Cpath d='M22.3026 29.1504C21.6526 29.3175 20.9713 29.4063 20.2692 29.4063C19.517 29.4063 18.7886 29.3043 18.0971 29.1134L15.2151 39.8692L19.1481 40.923L22.3026 29.1504Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3Cpath d='M17.9581 29.0737C16.5785 28.6661 15.3514 27.903 14.383 26.8904L6.45052 34.8229L9.32971 37.7021L17.9581 29.0737Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3Cpath d='M14.3168 26.8203C13.365 25.8013 12.6717 24.5377 12.3417 23.1341L1.38334 26.0704L2.43719 30.0034L14.3168 26.8203Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-55' width='168' height='41' viewBox='0 0 168 41' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M49.2775 28.9524H61.2295V25.3524H53.5255V11.7924H49.2775V28.9524Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M68.3107 26.5524C66.6067 26.5524 65.7187 25.0644 65.7187 22.8324C65.7187 20.6004 66.6067 19.0884 68.3107 19.0884C70.0147 19.0884 70.9267 20.6004 70.9267 22.8324C70.9267 25.0644 70.0147 26.5524 68.3107 26.5524ZM68.3347 29.3364C72.2947 29.3364 74.8867 26.5284 74.8867 22.8324C74.8867 19.1364 72.2947 16.3284 68.3347 16.3284C64.3987 16.3284 61.7587 19.1364 61.7587 22.8324C61.7587 26.5284 64.3987 29.3364 68.3347 29.3364Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M81.7411 33.2004C83.5651 33.2004 85.1731 32.7924 86.2531 31.8324C87.2371 30.9444 87.8851 29.6004 87.8851 27.7524V16.6644H84.1411V17.9844H84.0931C83.3731 16.9524 82.2691 16.3044 80.6371 16.3044C77.5891 16.3044 75.4771 18.8484 75.4771 22.4484C75.4771 26.2164 78.0451 28.2804 80.8051 28.2804C82.2931 28.2804 83.2291 27.6804 83.9491 26.8644H84.0451V28.0884C84.0451 29.5764 83.3491 30.4404 81.6931 30.4404C80.3971 30.4404 79.7491 29.8884 79.5331 29.2404H75.7411C76.1251 31.8084 78.3571 33.2004 81.7411 33.2004ZM81.7171 25.3764C80.2531 25.3764 79.2931 24.1764 79.2931 22.3284C79.2931 20.4564 80.2531 19.2564 81.7171 19.2564C83.3491 19.2564 84.2131 20.6484 84.2131 22.3044C84.2131 24.0324 83.4211 25.3764 81.7171 25.3764Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M95.5835 26.5524C93.8795 26.5524 92.9915 25.0644 92.9915 22.8324C92.9915 20.6004 93.8795 19.0884 95.5835 19.0884C97.2875 19.0884 98.1995 20.6004 98.1995 22.8324C98.1995 25.0644 97.2875 26.5524 95.5835 26.5524ZM95.6075 29.3364C99.5675 29.3364 102.159 26.5284 102.159 22.8324C102.159 19.1364 99.5675 16.3284 95.6075 16.3284C91.6715 16.3284 89.0315 19.1364 89.0315 22.8324C89.0315 26.5284 91.6715 29.3364 95.6075 29.3364Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M103.302 28.9524H107.214V16.6644H103.302V28.9524ZM103.302 14.9604H107.214V11.7924H103.302V14.9604Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M108.911 33.0084H112.823V27.6804H112.871C113.639 28.7124 114.767 29.3364 116.351 29.3364C119.567 29.3364 121.703 26.7924 121.703 22.8084C121.703 19.1124 119.711 16.3044 116.447 16.3044C114.767 16.3044 113.567 17.0484 112.727 18.1524H112.655V16.6644H108.911V33.0084ZM115.343 26.3124C113.663 26.3124 112.703 24.9444 112.703 22.9524C112.703 20.9604 113.567 19.4484 115.271 19.4484C116.951 19.4484 117.743 20.8404 117.743 22.9524C117.743 25.0404 116.831 26.3124 115.343 26.3124Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M128.072 29.3364C131.288 29.3364 133.664 27.9444 133.664 25.2564C133.664 22.1124 131.12 21.5604 128.96 21.2004C127.4 20.9124 126.008 20.7924 126.008 19.9284C126.008 19.1604 126.752 18.8004 127.712 18.8004C128.792 18.8004 129.536 19.1364 129.68 20.2404H133.28C133.088 17.8164 131.216 16.3044 127.736 16.3044C124.832 16.3044 122.432 17.6484 122.432 20.2404C122.432 23.1204 124.712 23.6964 126.848 24.0564C128.48 24.3444 129.968 24.4644 129.968 25.5684C129.968 26.3604 129.224 26.7924 128.048 26.7924C126.752 26.7924 125.936 26.1924 125.792 24.9684H122.096C122.216 27.6804 124.472 29.3364 128.072 29.3364Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M138.978 29.3124C140.682 29.3124 141.762 28.6404 142.65 27.4404H142.722V28.9524H146.466V16.6644H142.554V23.5284C142.554 24.9924 141.738 26.0004 140.394 26.0004C139.146 26.0004 138.546 25.2564 138.546 23.9124V16.6644H134.658V24.7284C134.658 27.4644 136.146 29.3124 138.978 29.3124Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M148.168 28.9524H152.08V22.0644C152.08 20.6004 152.8 19.5684 154.024 19.5684C155.2 19.5684 155.752 20.3364 155.752 21.6564V28.9524H159.664V22.0644C159.664 20.6004 160.36 19.5684 161.608 19.5684C162.784 19.5684 163.336 20.3364 163.336 21.6564V28.9524H167.248V20.9604C167.248 18.2004 165.856 16.3044 163.072 16.3044C161.488 16.3044 160.168 16.9764 159.208 18.4644H159.16C158.536 17.1444 157.312 16.3044 155.704 16.3044C153.928 16.3044 152.752 17.1444 151.984 18.4164H151.912V16.6644H148.168V28.9524Z' class='cneutral' fill='%233C2B1F'%3E%3C/path%3E%3Cpath d='M25.4099 1.97689L21.4769 0.923031L18.1625 13.2926L15.1702 2.12527L11.2371 3.17913L14.4701 15.2446L6.41746 7.19201L3.53827 10.0712L12.371 18.904L1.37124 15.9566L0.317383 19.8896L12.336 23.11C12.1984 22.5165 12.1256 21.8981 12.1256 21.2627C12.1256 16.7651 15.7716 13.1191 20.2692 13.1191C24.7668 13.1191 28.4128 16.7651 28.4128 21.2627C28.4128 21.894 28.3409 22.5086 28.205 23.0986L39.1277 26.0253L40.1815 22.0923L28.1151 18.8591L39.1156 15.9115L38.0617 11.9785L25.9958 15.2115L34.0484 7.15895L31.1692 4.27976L22.459 12.99L25.4099 1.97689Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3Cpath d='M28.1943 23.1444C27.8571 24.57 27.1452 25.8507 26.1684 26.8768L34.0814 34.7899L36.9606 31.9107L28.1943 23.1444Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3Cpath d='M26.0884 26.9596C25.0998 27.9693 23.8505 28.7228 22.4495 29.1111L25.3289 39.8571L29.2619 38.8032L26.0884 26.9596Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3Cpath d='M22.3026 29.1504C21.6526 29.3175 20.9713 29.4063 20.2692 29.4063C19.517 29.4063 18.7886 29.3043 18.0971 29.1134L15.2151 39.8692L19.1481 40.923L22.3026 29.1504Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3Cpath d='M17.9581 29.0737C16.5785 28.6661 15.3514 27.903 14.383 26.8904L6.45052 34.8229L9.32971 37.7021L17.9581 29.0737Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3Cpath d='M14.3168 26.8203C13.365 25.8013 12.6717 24.5377 12.3417 23.1341L1.38334 26.0704L2.43719 30.0034L14.3168 26.8203Z' class='ccustom' fill='%23F97316'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-44' width='172' height='40' viewBox='0 0 172 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M49.0364 29H60.3891V25.7673H52.4982V10.6727H49.0364V29Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M67.2113 29.3818C68.5859 29.3818 69.795 29.0763 70.8386 28.4654C71.8907 27.846 72.7095 26.9933 73.295 25.9073C73.8889 24.8127 74.1859 23.5527 74.1859 22.1273C74.1859 20.7103 73.8931 19.4588 73.3077 18.3727C72.7222 17.2782 71.9034 16.4212 70.8513 15.8018C69.8077 15.1824 68.5944 14.8727 67.2113 14.8727C65.8537 14.8727 64.6531 15.1782 63.6095 15.7891C62.5659 16.4 61.7471 17.2527 61.1531 18.3473C60.5592 19.4333 60.2622 20.6933 60.2622 22.1273C60.2622 23.5442 60.5507 24.8 61.1277 25.8945C61.7131 26.9806 62.5277 27.8333 63.5713 28.4527C64.615 29.0721 65.8283 29.3818 67.2113 29.3818ZM67.2113 26.1491C66.1337 26.1491 65.315 25.7885 64.755 25.0673C64.2034 24.3376 63.9277 23.3576 63.9277 22.1273C63.9277 20.9309 64.1907 19.9636 64.7168 19.2254C65.2513 18.4788 66.0828 18.1054 67.2113 18.1054C68.3059 18.1054 69.1289 18.4703 69.6804 19.2C70.2404 19.9297 70.5204 20.9054 70.5204 22.1273C70.5204 23.3067 70.2447 24.2739 69.6931 25.0291C69.1501 25.7757 68.3228 26.1491 67.2113 26.1491Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M81.0319 29.3818C81.6768 29.3818 82.2707 29.3054 82.8138 29.1527C83.3653 29 83.8659 28.7836 84.3156 28.5036V29.8909C84.3326 30.4 84.201 30.8242 83.921 31.1636C83.6495 31.5115 83.2847 31.7703 82.8265 31.94C82.3683 32.1182 81.8804 32.2073 81.3629 32.2073C80.8792 32.2073 80.4295 32.1012 80.0138 31.8891C79.6065 31.677 79.2925 31.3673 79.0719 30.96L75.8647 32.5127C76.3907 33.4036 77.1416 34.1206 78.1174 34.6636C79.0932 35.2151 80.1665 35.4909 81.3374 35.4909C82.3471 35.4909 83.2847 35.3551 84.1501 35.0836C85.0156 34.8206 85.7453 34.4176 86.3392 33.8745C86.9416 33.3315 87.3532 32.64 87.5738 31.8C87.6501 31.503 87.701 31.2018 87.7265 30.8963C87.7604 30.5994 87.7774 30.2812 87.7774 29.9418V15.2545H84.7483V16.0182C84.2816 15.6533 83.7513 15.3733 83.1574 15.1782C82.5719 14.9745 81.9229 14.8727 81.2101 14.8727C79.895 14.8727 78.7495 15.1867 77.7738 15.8145C76.798 16.4424 76.0386 17.3036 75.4956 18.3982C74.961 19.4842 74.6938 20.7273 74.6938 22.1273C74.6938 23.5018 74.9568 24.7363 75.4829 25.8309C76.0174 26.9254 76.7598 27.7909 77.7101 28.4273C78.6604 29.0636 79.7677 29.3818 81.0319 29.3818ZM81.5919 26.3018C80.8453 26.3018 80.2344 26.1151 79.7592 25.7418C79.2841 25.3685 78.9319 24.8679 78.7029 24.24C78.4738 23.6036 78.3592 22.8994 78.3592 22.1273C78.3592 21.3636 78.478 20.6679 78.7156 20.04C78.9532 19.4036 79.318 18.8988 79.8101 18.5254C80.3107 18.1436 80.9471 17.9527 81.7192 17.9527C82.8053 17.9527 83.5816 18.3388 84.0483 19.1109C84.515 19.8745 84.7483 20.88 84.7483 22.1273C84.7483 23.3745 84.5107 24.3842 84.0356 25.1563C83.5689 25.92 82.7544 26.3018 81.5919 26.3018Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M95.9998 29.3818C97.3744 29.3818 98.5835 29.0763 99.6271 28.4654C100.679 27.846 101.498 26.9933 102.083 25.9073C102.677 24.8127 102.974 23.5527 102.974 22.1273C102.974 20.7103 102.682 19.4588 102.096 18.3727C101.511 17.2782 100.692 16.4212 99.6398 15.8018C98.5962 15.1824 97.3828 14.8727 95.9998 14.8727C94.6422 14.8727 93.4416 15.1782 92.398 15.7891C91.3544 16.4 90.5356 17.2527 89.9416 18.3473C89.3477 19.4333 89.0507 20.6933 89.0507 22.1273C89.0507 23.5442 89.3392 24.8 89.9162 25.8945C90.5016 26.9806 91.3162 27.8333 92.3598 28.4527C93.4035 29.0721 94.6168 29.3818 95.9998 29.3818ZM95.9998 26.1491C94.9222 26.1491 94.1034 25.7885 93.5434 25.0673C92.9919 24.3376 92.7162 23.3576 92.7162 22.1273C92.7162 20.9309 92.9792 19.9636 93.5053 19.2254C94.0398 18.4788 94.8713 18.1054 95.9998 18.1054C97.0944 18.1054 97.9174 18.4703 98.4689 19.2C99.0289 19.9297 99.3089 20.9054 99.3089 22.1273C99.3089 23.3067 99.0331 24.2739 98.4816 25.0291C97.9386 25.7757 97.1113 26.1491 95.9998 26.1491Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M104.5 13.3454H107.962V10.2909H104.5V13.3454ZM104.5 29H107.962V15.2545H104.5V29Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M110.225 35.1091H113.712V28.5036C114.162 28.7836 114.658 29 115.201 29.1527C115.753 29.3054 116.351 29.3818 116.996 29.3818C118.26 29.3818 119.368 29.0636 120.318 28.4273C121.268 27.7909 122.006 26.9254 122.532 25.8309C123.067 24.7363 123.334 23.5018 123.334 22.1273C123.334 20.7273 123.063 19.4842 122.52 18.3982C121.985 17.3036 121.23 16.4424 120.254 15.8145C119.278 15.1867 118.133 14.8727 116.818 14.8727C116.105 14.8727 115.452 14.9745 114.858 15.1782C114.272 15.3733 113.746 15.6533 113.28 16.0182V15.2545H110.225V35.1091ZM116.436 26.3018C115.282 26.3018 114.468 25.92 113.992 25.1563C113.517 24.3842 113.28 23.3745 113.28 22.1273C113.28 20.88 113.513 19.8745 113.98 19.1109C114.455 18.3388 115.231 17.9527 116.309 17.9527C117.081 17.9527 117.713 18.1436 118.205 18.5254C118.706 18.8988 119.075 19.4036 119.312 20.04C119.55 20.6679 119.669 21.3636 119.669 22.1273C119.669 22.8994 119.554 23.6036 119.325 24.24C119.096 24.8679 118.744 25.3685 118.269 25.7418C117.794 26.1151 117.183 26.3018 116.436 26.3018Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M129.606 29.3818C131.404 29.3818 132.813 28.9788 133.831 28.1727C134.849 27.3666 135.358 26.2594 135.358 24.8509C135.358 23.7818 135.027 22.9376 134.366 22.3182C133.712 21.6988 132.601 21.1854 131.031 20.7782C129.962 20.5066 129.164 20.286 128.638 20.1163C128.121 19.9467 127.777 19.7812 127.607 19.62C127.446 19.4588 127.366 19.2594 127.366 19.0218C127.366 18.623 127.556 18.3176 127.938 18.1054C128.329 17.8933 128.842 17.8085 129.478 17.8509C130.827 17.9527 131.566 18.5297 131.693 19.5818L135.231 18.9454C135.053 17.6982 134.442 16.7097 133.398 15.98C132.355 15.2418 131.023 14.8727 129.402 14.8727C127.739 14.8727 126.411 15.263 125.418 16.0436C124.426 16.8242 123.929 17.8763 123.929 19.2C123.929 20.2521 124.273 21.0836 124.96 21.6945C125.647 22.297 126.831 22.8145 128.511 23.2473C129.504 23.5103 130.233 23.7224 130.7 23.8836C131.175 24.0448 131.481 24.2103 131.616 24.38C131.752 24.5412 131.82 24.7576 131.82 25.0291C131.82 25.4618 131.65 25.8012 131.311 26.0473C130.972 26.2848 130.488 26.4036 129.86 26.4036C129.096 26.4036 128.464 26.2212 127.964 25.8563C127.472 25.4915 127.153 24.9867 127.009 24.3418L123.471 24.8763C123.7 26.3103 124.345 27.4218 125.406 28.2109C126.475 28.9915 127.875 29.3818 129.606 29.3818Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M141.744 29.4073C142.737 29.4073 143.602 29.2418 144.341 28.9109C145.079 28.58 145.698 28.1388 146.199 27.5873V29H149.253V15.2545H145.766V22.2291C145.766 23.0776 145.668 23.7648 145.473 24.2909C145.287 24.8085 145.045 25.203 144.748 25.4745C144.451 25.7376 144.133 25.9157 143.793 26.0091C143.454 26.1024 143.136 26.1491 142.839 26.1491C142.101 26.1491 141.528 25.9836 141.121 25.6527C140.722 25.3218 140.433 24.9103 140.255 24.4182C140.077 23.926 139.971 23.4382 139.937 22.9545C139.903 22.4624 139.886 22.0594 139.886 21.7454V15.2545H136.373V22.9673C136.373 23.1963 136.39 23.5612 136.424 24.0618C136.458 24.5624 136.556 25.1182 136.717 25.7291C136.878 26.3315 137.145 26.9127 137.519 27.4727C137.901 28.0327 138.431 28.4951 139.11 28.86C139.788 29.2248 140.667 29.4073 141.744 29.4073Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M151.258 29H154.745V20.6763C154.745 19.8873 154.961 19.2467 155.394 18.7545C155.835 18.2539 156.416 18.0036 157.138 18.0036C157.893 18.0036 158.483 18.2582 158.907 18.7673C159.339 19.2679 159.556 19.9721 159.556 20.88V29H163.018V20.6763C163.018 19.8873 163.234 19.2467 163.667 18.7545C164.108 18.2539 164.689 18.0036 165.41 18.0036C166.166 18.0036 166.755 18.2582 167.179 18.7673C167.612 19.2679 167.829 19.9721 167.829 20.88V29H171.29V19.9636C171.29 18.4618 170.887 17.2485 170.081 16.3236C169.284 15.3903 168.1 14.9236 166.53 14.9236C165.648 14.9236 164.838 15.1145 164.099 15.4963C163.361 15.8782 162.772 16.4 162.33 17.0618C161.974 16.417 161.465 15.8994 160.803 15.5091C160.141 15.1188 159.318 14.9236 158.334 14.9236C157.502 14.9236 156.739 15.0891 156.043 15.42C155.347 15.7424 154.77 16.1879 154.312 16.7563V15.2545H151.258V29Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M20 0C8.9543 0 0 8.9543 0 20C11.0457 20 20 11.0457 20 0Z' fill='%2345D2B0' class='ccustom'%3E%3C/path%3E%3Cpath d='M20 40C31.0457 40 40 31.0457 40 20C28.9543 20 20 28.9543 20 40Z' fill='%2345D2B0' class='ccustom'%3E%3C/path%3E%3Cpath d='M20 0C31.0457 0 40 8.9543 40 20C28.9543 20 20 11.0457 20 0Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M20 40C8.9543 40 -9.65645e-07 31.0457 0 20C11.0457 20 20 28.9543 20 40Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-44' width='172' height='40' viewBox='0 0 172 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M49.0364 29H60.3891V25.7673H52.4982V10.6727H49.0364V29Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M67.2113 29.3818C68.5859 29.3818 69.795 29.0763 70.8386 28.4654C71.8907 27.846 72.7095 26.9933 73.295 25.9073C73.8889 24.8127 74.1859 23.5527 74.1859 22.1273C74.1859 20.7103 73.8931 19.4588 73.3077 18.3727C72.7222 17.2782 71.9034 16.4212 70.8513 15.8018C69.8077 15.1824 68.5944 14.8727 67.2113 14.8727C65.8537 14.8727 64.6531 15.1782 63.6095 15.7891C62.5659 16.4 61.7471 17.2527 61.1531 18.3473C60.5592 19.4333 60.2622 20.6933 60.2622 22.1273C60.2622 23.5442 60.5507 24.8 61.1277 25.8945C61.7131 26.9806 62.5277 27.8333 63.5713 28.4527C64.615 29.0721 65.8283 29.3818 67.2113 29.3818ZM67.2113 26.1491C66.1337 26.1491 65.315 25.7885 64.755 25.0673C64.2034 24.3376 63.9277 23.3576 63.9277 22.1273C63.9277 20.9309 64.1907 19.9636 64.7168 19.2254C65.2513 18.4788 66.0828 18.1054 67.2113 18.1054C68.3059 18.1054 69.1289 18.4703 69.6804 19.2C70.2404 19.9297 70.5204 20.9054 70.5204 22.1273C70.5204 23.3067 70.2447 24.2739 69.6931 25.0291C69.1501 25.7757 68.3228 26.1491 67.2113 26.1491Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M81.0319 29.3818C81.6768 29.3818 82.2707 29.3054 82.8138 29.1527C83.3653 29 83.8659 28.7836 84.3156 28.5036V29.8909C84.3326 30.4 84.201 30.8242 83.921 31.1636C83.6495 31.5115 83.2847 31.7703 82.8265 31.94C82.3683 32.1182 81.8804 32.2073 81.3629 32.2073C80.8792 32.2073 80.4295 32.1012 80.0138 31.8891C79.6065 31.677 79.2925 31.3673 79.0719 30.96L75.8647 32.5127C76.3907 33.4036 77.1416 34.1206 78.1174 34.6636C79.0932 35.2151 80.1665 35.4909 81.3374 35.4909C82.3471 35.4909 83.2847 35.3551 84.1501 35.0836C85.0156 34.8206 85.7453 34.4176 86.3392 33.8745C86.9416 33.3315 87.3532 32.64 87.5738 31.8C87.6501 31.503 87.701 31.2018 87.7265 30.8963C87.7604 30.5994 87.7774 30.2812 87.7774 29.9418V15.2545H84.7483V16.0182C84.2816 15.6533 83.7513 15.3733 83.1574 15.1782C82.5719 14.9745 81.9229 14.8727 81.2101 14.8727C79.895 14.8727 78.7495 15.1867 77.7738 15.8145C76.798 16.4424 76.0386 17.3036 75.4956 18.3982C74.961 19.4842 74.6938 20.7273 74.6938 22.1273C74.6938 23.5018 74.9568 24.7363 75.4829 25.8309C76.0174 26.9254 76.7598 27.7909 77.7101 28.4273C78.6604 29.0636 79.7677 29.3818 81.0319 29.3818ZM81.5919 26.3018C80.8453 26.3018 80.2344 26.1151 79.7592 25.7418C79.2841 25.3685 78.9319 24.8679 78.7029 24.24C78.4738 23.6036 78.3592 22.8994 78.3592 22.1273C78.3592 21.3636 78.478 20.6679 78.7156 20.04C78.9532 19.4036 79.318 18.8988 79.8101 18.5254C80.3107 18.1436 80.9471 17.9527 81.7192 17.9527C82.8053 17.9527 83.5816 18.3388 84.0483 19.1109C84.515 19.8745 84.7483 20.88 84.7483 22.1273C84.7483 23.3745 84.5107 24.3842 84.0356 25.1563C83.5689 25.92 82.7544 26.3018 81.5919 26.3018Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M95.9998 29.3818C97.3744 29.3818 98.5835 29.0763 99.6271 28.4654C100.679 27.846 101.498 26.9933 102.083 25.9073C102.677 24.8127 102.974 23.5527 102.974 22.1273C102.974 20.7103 102.682 19.4588 102.096 18.3727C101.511 17.2782 100.692 16.4212 99.6398 15.8018C98.5962 15.1824 97.3828 14.8727 95.9998 14.8727C94.6422 14.8727 93.4416 15.1782 92.398 15.7891C91.3544 16.4 90.5356 17.2527 89.9416 18.3473C89.3477 19.4333 89.0507 20.6933 89.0507 22.1273C89.0507 23.5442 89.3392 24.8 89.9162 25.8945C90.5016 26.9806 91.3162 27.8333 92.3598 28.4527C93.4035 29.0721 94.6168 29.3818 95.9998 29.3818ZM95.9998 26.1491C94.9222 26.1491 94.1034 25.7885 93.5434 25.0673C92.9919 24.3376 92.7162 23.3576 92.7162 22.1273C92.7162 20.9309 92.9792 19.9636 93.5053 19.2254C94.0398 18.4788 94.8713 18.1054 95.9998 18.1054C97.0944 18.1054 97.9174 18.4703 98.4689 19.2C99.0289 19.9297 99.3089 20.9054 99.3089 22.1273C99.3089 23.3067 99.0331 24.2739 98.4816 25.0291C97.9386 25.7757 97.1113 26.1491 95.9998 26.1491Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M104.5 13.3454H107.962V10.2909H104.5V13.3454ZM104.5 29H107.962V15.2545H104.5V29Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M110.225 35.1091H113.712V28.5036C114.162 28.7836 114.658 29 115.201 29.1527C115.753 29.3054 116.351 29.3818 116.996 29.3818C118.26 29.3818 119.368 29.0636 120.318 28.4273C121.268 27.7909 122.006 26.9254 122.532 25.8309C123.067 24.7363 123.334 23.5018 123.334 22.1273C123.334 20.7273 123.063 19.4842 122.52 18.3982C121.985 17.3036 121.23 16.4424 120.254 15.8145C119.278 15.1867 118.133 14.8727 116.818 14.8727C116.105 14.8727 115.452 14.9745 114.858 15.1782C114.272 15.3733 113.746 15.6533 113.28 16.0182V15.2545H110.225V35.1091ZM116.436 26.3018C115.282 26.3018 114.468 25.92 113.992 25.1563C113.517 24.3842 113.28 23.3745 113.28 22.1273C113.28 20.88 113.513 19.8745 113.98 19.1109C114.455 18.3388 115.231 17.9527 116.309 17.9527C117.081 17.9527 117.713 18.1436 118.205 18.5254C118.706 18.8988 119.075 19.4036 119.312 20.04C119.55 20.6679 119.669 21.3636 119.669 22.1273C119.669 22.8994 119.554 23.6036 119.325 24.24C119.096 24.8679 118.744 25.3685 118.269 25.7418C117.794 26.1151 117.183 26.3018 116.436 26.3018Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M129.606 29.3818C131.404 29.3818 132.813 28.9788 133.831 28.1727C134.849 27.3666 135.358 26.2594 135.358 24.8509C135.358 23.7818 135.027 22.9376 134.366 22.3182C133.712 21.6988 132.601 21.1854 131.031 20.7782C129.962 20.5066 129.164 20.286 128.638 20.1163C128.121 19.9467 127.777 19.7812 127.607 19.62C127.446 19.4588 127.366 19.2594 127.366 19.0218C127.366 18.623 127.556 18.3176 127.938 18.1054C128.329 17.8933 128.842 17.8085 129.478 17.8509C130.827 17.9527 131.566 18.5297 131.693 19.5818L135.231 18.9454C135.053 17.6982 134.442 16.7097 133.398 15.98C132.355 15.2418 131.023 14.8727 129.402 14.8727C127.739 14.8727 126.411 15.263 125.418 16.0436C124.426 16.8242 123.929 17.8763 123.929 19.2C123.929 20.2521 124.273 21.0836 124.96 21.6945C125.647 22.297 126.831 22.8145 128.511 23.2473C129.504 23.5103 130.233 23.7224 130.7 23.8836C131.175 24.0448 131.481 24.2103 131.616 24.38C131.752 24.5412 131.82 24.7576 131.82 25.0291C131.82 25.4618 131.65 25.8012 131.311 26.0473C130.972 26.2848 130.488 26.4036 129.86 26.4036C129.096 26.4036 128.464 26.2212 127.964 25.8563C127.472 25.4915 127.153 24.9867 127.009 24.3418L123.471 24.8763C123.7 26.3103 124.345 27.4218 125.406 28.2109C126.475 28.9915 127.875 29.3818 129.606 29.3818Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M141.744 29.4073C142.737 29.4073 143.602 29.2418 144.341 28.9109C145.079 28.58 145.698 28.1388 146.199 27.5873V29H149.253V15.2545H145.766V22.2291C145.766 23.0776 145.668 23.7648 145.473 24.2909C145.287 24.8085 145.045 25.203 144.748 25.4745C144.451 25.7376 144.133 25.9157 143.793 26.0091C143.454 26.1024 143.136 26.1491 142.839 26.1491C142.101 26.1491 141.528 25.9836 141.121 25.6527C140.722 25.3218 140.433 24.9103 140.255 24.4182C140.077 23.926 139.971 23.4382 139.937 22.9545C139.903 22.4624 139.886 22.0594 139.886 21.7454V15.2545H136.373V22.9673C136.373 23.1963 136.39 23.5612 136.424 24.0618C136.458 24.5624 136.556 25.1182 136.717 25.7291C136.878 26.3315 137.145 26.9127 137.519 27.4727C137.901 28.0327 138.431 28.4951 139.11 28.86C139.788 29.2248 140.667 29.4073 141.744 29.4073Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M151.258 29H154.745V20.6763C154.745 19.8873 154.961 19.2467 155.394 18.7545C155.835 18.2539 156.416 18.0036 157.138 18.0036C157.893 18.0036 158.483 18.2582 158.907 18.7673C159.339 19.2679 159.556 19.9721 159.556 20.88V29H163.018V20.6763C163.018 19.8873 163.234 19.2467 163.667 18.7545C164.108 18.2539 164.689 18.0036 165.41 18.0036C166.166 18.0036 166.755 18.2582 167.179 18.7673C167.612 19.2679 167.829 19.9721 167.829 20.88V29H171.29V19.9636C171.29 18.4618 170.887 17.2485 170.081 16.3236C169.284 15.3903 168.1 14.9236 166.53 14.9236C165.648 14.9236 164.838 15.1145 164.099 15.4963C163.361 15.8782 162.772 16.4 162.33 17.0618C161.974 16.417 161.465 15.8994 160.803 15.5091C160.141 15.1188 159.318 14.9236 158.334 14.9236C157.502 14.9236 156.739 15.0891 156.043 15.42C155.347 15.7424 154.77 16.1879 154.312 16.7563V15.2545H151.258V29Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M20 0C8.9543 0 0 8.9543 0 20C11.0457 20 20 11.0457 20 0Z' fill='%2345D2B0' class='ccustom'%3E%3C/path%3E%3Cpath d='M20 40C31.0457 40 40 31.0457 40 20C28.9543 20 20 28.9543 20 40Z' fill='%2345D2B0' class='ccustom'%3E%3C/path%3E%3Cpath d='M20 0C31.0457 0 40 8.9543 40 20C28.9543 20 20 11.0457 20 0Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3Cpath d='M20 40C8.9543 40 -9.65645e-07 31.0457 0 20C11.0457 20 20 28.9543 20 40Z' fill='%2323216E' class='ccompli2'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-5' width='132' height='40' viewBox='0 0 132 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M23.23 11.39H25.23V25.31H31.23V27.31H23.23V11.39ZM37.46 11.39C38.6467 11.39 39.8067 11.7419 40.7934 12.4012C41.7801 13.0605 42.5492 13.9975 43.0033 15.0939C43.4574 16.1903 43.5762 17.3967 43.3447 18.5605C43.1132 19.7244 42.5418 20.7935 41.7026 21.6326C40.8635 22.4718 39.7944 23.0432 38.6305 23.2747C37.4667 23.5062 36.2603 23.3874 35.1639 22.9333C34.0675 22.4791 33.1305 21.7101 32.4712 20.7234C31.8119 19.7367 31.46 18.5767 31.46 17.39C31.46 16.6021 31.6152 15.8218 31.9167 15.0939C32.2182 14.3659 32.6602 13.7045 33.2174 13.1474C33.7745 12.5902 34.4359 12.1482 35.1639 11.8467C35.8918 11.5452 36.6721 11.39 37.46 11.39V11.39ZM37.46 21.39C38.2511 21.39 39.0245 21.1554 39.6823 20.7159C40.3401 20.2763 40.8528 19.6516 41.1555 18.9207C41.4583 18.1898 41.5375 17.3856 41.3831 16.6096C41.2288 15.8337 40.8478 15.121 40.2884 14.5616C39.729 14.0022 39.0163 13.6212 38.2404 13.4669C37.4644 13.3125 36.6602 13.3917 35.9293 13.6945C35.1984 13.9972 34.5736 14.5099 34.1341 15.1677C33.6946 15.8255 33.46 16.5989 33.46 17.39C33.4653 18.4474 33.889 19.4597 34.6386 20.2055C35.3882 20.9513 36.4026 21.37 37.46 21.37V21.39ZM33.46 25.33H41.46V27.33H33.46V25.33ZM59.06 27.33H57.06V25.9C55.7702 26.8028 54.2344 27.288 52.66 27.29C51.3175 27.299 49.9943 26.97 48.8124 26.3333C47.6304 25.6965 46.6277 24.7726 45.8967 23.6466C45.1656 22.5206 44.7296 21.2287 44.629 19.8899C44.5283 18.5512 44.7662 17.2086 45.3207 15.986C45.8752 14.7633 46.7285 13.6998 47.8019 12.8936C48.8754 12.0873 50.1345 11.5641 51.4632 11.3723C52.792 11.1804 54.1477 11.3261 55.4053 11.7958C56.663 12.2655 57.7823 13.0441 58.66 14.06L57.19 15.37C56.5224 14.6236 55.6787 14.0562 54.7356 13.7195C53.7926 13.3827 52.7803 13.2873 51.791 13.442C50.8016 13.5967 49.8668 13.9966 49.0715 14.6051C48.2763 15.2137 47.646 16.0115 47.2382 16.9261C46.8303 17.8406 46.6578 18.8426 46.7364 19.8409C46.815 20.8392 47.1421 21.8019 47.6881 22.6413C48.2341 23.4807 48.9814 24.1702 49.8621 24.6468C50.7427 25.1234 51.7287 25.372 52.73 25.37C53.561 25.3717 54.3826 25.1939 55.1386 24.8487C55.8945 24.5035 56.567 23.9991 57.11 23.37H51.71V21.37H59.08L59.06 27.33ZM66.42 11.43C67.6067 11.43 68.7667 11.7819 69.7534 12.4412C70.7401 13.1005 71.5092 14.0375 71.9633 15.1339C72.4174 16.2303 72.5362 17.4367 72.3047 18.6005C72.0732 19.7644 71.5018 20.8335 70.6626 21.6726C69.8235 22.5118 68.7544 23.0832 67.5905 23.3147C66.4267 23.5462 65.2203 23.4274 64.1239 22.9733C63.0275 22.5191 62.0905 21.7501 61.4312 20.7634C60.7719 19.7767 60.42 18.6167 60.42 17.43C60.4147 16.637 60.5667 15.8509 60.8671 15.117C61.1675 14.3831 61.6104 13.716 62.1702 13.1544C62.73 12.5927 63.3956 12.1476 64.1285 11.8447C64.8614 11.5419 65.647 11.3873 66.44 11.39L66.42 11.43ZM66.42 21.43C67.2111 21.43 67.9845 21.1954 68.6423 20.7559C69.3001 20.3163 69.8128 19.6916 70.1155 18.9607C70.4183 18.2298 70.4975 17.4256 70.3431 16.6496C70.1888 15.8737 69.8078 15.161 69.2484 14.6016C68.689 14.0422 67.9763 13.6612 67.2004 13.5069C66.4244 13.3525 65.6202 13.4317 64.8893 13.7345C64.1584 14.0372 63.5336 14.5499 63.0941 15.2077C62.6546 15.8655 62.42 16.6389 62.42 17.43C62.4358 18.4839 62.8669 19.489 63.6197 20.2268C64.3724 20.9645 65.386 21.3754 66.44 21.37L66.42 21.43ZM62.42 25.37H70.42V27.37H62.42V25.37ZM74.55 11.39H76.55V27.29H74.55V11.39ZM79.32 11.39H81.32C81.423 11.3791 81.5269 11.3791 81.63 11.39C82.4676 11.2991 83.315 11.3857 84.1169 11.644C84.9188 11.9024 85.6574 12.3267 86.2844 12.8894C86.9115 13.4521 87.413 14.1406 87.7563 14.91C88.0997 15.6794 88.2771 16.5125 88.2771 17.355C88.2771 18.1975 88.0997 19.0306 87.7563 19.8C87.413 20.5694 86.9115 21.2579 86.2844 21.8206C85.6574 22.3833 84.9188 22.8076 84.1169 23.066C83.315 23.3243 82.4676 23.4109 81.63 23.32H81.32V27.32H79.32V11.39ZM81.32 13.39V21.3H81.63C82.1949 21.3752 82.7693 21.3289 83.3149 21.164C83.8604 20.9992 84.3644 20.7197 84.7931 20.3443C85.2219 19.9689 85.5654 19.5062 85.8008 18.9872C86.0362 18.4682 86.158 17.9049 86.158 17.335C86.158 16.7651 86.0362 16.2018 85.8008 15.6828C85.5654 15.1638 85.2219 14.7011 84.7931 14.3257C84.3644 13.9502 83.8604 13.6708 83.3149 13.5059C82.7693 13.3411 82.1949 13.2948 81.63 13.37C81.5211 13.3813 81.4137 13.4048 81.31 13.44L81.32 13.39ZM95.73 12.54L94.25 13.71C93.9947 13.4432 93.6685 13.2548 93.3098 13.167C92.9511 13.0792 92.5748 13.0956 92.2251 13.2143C91.8753 13.3329 91.5668 13.5489 91.3356 13.8369C91.1044 14.1249 90.9602 14.4729 90.92 14.84V15C90.92 15.88 91.53 16.47 92.72 16.55C97.3 16.83 99.4 18.98 99.4 21.82V22C99.2817 23.124 98.8431 24.1904 98.1363 25.0724C97.4295 25.9544 96.4842 26.6147 95.413 26.975C94.3417 27.3352 93.1895 27.3802 92.0934 27.1045C90.9973 26.8289 90.0034 26.2442 89.23 25.42L90.76 24.24C91.1161 24.6217 91.551 24.9213 92.0345 25.1182C92.518 25.315 93.0385 25.4044 93.56 25.38C94.5232 25.4308 95.4687 25.1075 96.1991 24.4776C96.9296 23.8478 97.3885 22.9601 97.48 22V21.86C97.48 19.19 94.86 18.7 92.59 18.48C90.49 18.28 88.98 16.97 88.98 15.08V15C89.054 14.016 89.5031 13.098 90.2344 12.4356C90.9657 11.7731 91.9235 11.4167 92.91 11.44C93.4328 11.4246 93.9529 11.5189 94.437 11.717C94.921 11.9151 95.3581 12.2125 95.72 12.59L95.73 12.54ZM107.23 25.26C109.72 25.26 111.69 22.57 111.69 19.26V11.26H113.69V19.26C113.69 23.66 110.81 27.21 107.27 27.21C103.73 27.21 100.85 23.66 100.85 19.26V11.26H102.85V19.26C102.77 22.62 104.74 25.31 107.22 25.31L107.23 25.26ZM129.04 27.26H127.04V17.36L122.43 23.36L117.82 17.36V27.29H115.82V11.39L122.42 20.08L129.02 11.39L129.04 27.26Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M13.63 9C13.63 7.55722 13.0569 6.17353 12.0367 5.15334C11.0165 4.13314 9.63278 3.56 8.19 3.56C6.74722 3.56 5.36354 4.13314 4.34334 5.15334C3.32314 6.17353 2.75 7.55722 2.75 9V25.45L7.23 28.66V36.48H9.15V28.66L13.63 25.45V9ZM11.71 18.2L9.15 20.76V18.36L11.71 15.8V18.2ZM4.71 15.8L7.27 18.36V20.76L4.71 18.2V15.8ZM11.71 13.08L8.19 16.6L4.67 13V10.6L8.19 14.12L11.71 10.6V13.08ZM8.19 5.48C8.96415 5.48342 9.71583 5.74053 10.3299 6.21193C10.944 6.68333 11.3866 7.34303 11.59 8.09L8.19 11.48L4.79 8.09C4.98594 7.3356 5.42537 6.66695 6.04013 6.18781C6.65489 5.70866 7.41059 5.44579 8.19 5.43999V5.48ZM4.67 24.48V20.88L7.23 23.44V26.3L4.67 24.48ZM9.15 26.31V23.44L11.71 20.88V24.47L9.15 26.31Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-5' width='132' height='40' viewBox='0 0 132 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M23.23 11.39H25.23V25.31H31.23V27.31H23.23V11.39ZM37.46 11.39C38.6467 11.39 39.8067 11.7419 40.7934 12.4012C41.7801 13.0605 42.5492 13.9975 43.0033 15.0939C43.4574 16.1903 43.5762 17.3967 43.3447 18.5605C43.1132 19.7244 42.5418 20.7935 41.7026 21.6326C40.8635 22.4718 39.7944 23.0432 38.6305 23.2747C37.4667 23.5062 36.2603 23.3874 35.1639 22.9333C34.0675 22.4791 33.1305 21.7101 32.4712 20.7234C31.8119 19.7367 31.46 18.5767 31.46 17.39C31.46 16.6021 31.6152 15.8218 31.9167 15.0939C32.2182 14.3659 32.6602 13.7045 33.2174 13.1474C33.7745 12.5902 34.4359 12.1482 35.1639 11.8467C35.8918 11.5452 36.6721 11.39 37.46 11.39V11.39ZM37.46 21.39C38.2511 21.39 39.0245 21.1554 39.6823 20.7159C40.3401 20.2763 40.8528 19.6516 41.1555 18.9207C41.4583 18.1898 41.5375 17.3856 41.3831 16.6096C41.2288 15.8337 40.8478 15.121 40.2884 14.5616C39.729 14.0022 39.0163 13.6212 38.2404 13.4669C37.4644 13.3125 36.6602 13.3917 35.9293 13.6945C35.1984 13.9972 34.5736 14.5099 34.1341 15.1677C33.6946 15.8255 33.46 16.5989 33.46 17.39C33.4653 18.4474 33.889 19.4597 34.6386 20.2055C35.3882 20.9513 36.4026 21.37 37.46 21.37V21.39ZM33.46 25.33H41.46V27.33H33.46V25.33ZM59.06 27.33H57.06V25.9C55.7702 26.8028 54.2344 27.288 52.66 27.29C51.3175 27.299 49.9943 26.97 48.8124 26.3333C47.6304 25.6965 46.6277 24.7726 45.8967 23.6466C45.1656 22.5206 44.7296 21.2287 44.629 19.8899C44.5283 18.5512 44.7662 17.2086 45.3207 15.986C45.8752 14.7633 46.7285 13.6998 47.8019 12.8936C48.8754 12.0873 50.1345 11.5641 51.4632 11.3723C52.792 11.1804 54.1477 11.3261 55.4053 11.7958C56.663 12.2655 57.7823 13.0441 58.66 14.06L57.19 15.37C56.5224 14.6236 55.6787 14.0562 54.7356 13.7195C53.7926 13.3827 52.7803 13.2873 51.791 13.442C50.8016 13.5967 49.8668 13.9966 49.0715 14.6051C48.2763 15.2137 47.646 16.0115 47.2382 16.9261C46.8303 17.8406 46.6578 18.8426 46.7364 19.8409C46.815 20.8392 47.1421 21.8019 47.6881 22.6413C48.2341 23.4807 48.9814 24.1702 49.8621 24.6468C50.7427 25.1234 51.7287 25.372 52.73 25.37C53.561 25.3717 54.3826 25.1939 55.1386 24.8487C55.8945 24.5035 56.567 23.9991 57.11 23.37H51.71V21.37H59.08L59.06 27.33ZM66.42 11.43C67.6067 11.43 68.7667 11.7819 69.7534 12.4412C70.7401 13.1005 71.5092 14.0375 71.9633 15.1339C72.4174 16.2303 72.5362 17.4367 72.3047 18.6005C72.0732 19.7644 71.5018 20.8335 70.6626 21.6726C69.8235 22.5118 68.7544 23.0832 67.5905 23.3147C66.4267 23.5462 65.2203 23.4274 64.1239 22.9733C63.0275 22.5191 62.0905 21.7501 61.4312 20.7634C60.7719 19.7767 60.42 18.6167 60.42 17.43C60.4147 16.637 60.5667 15.8509 60.8671 15.117C61.1675 14.3831 61.6104 13.716 62.1702 13.1544C62.73 12.5927 63.3956 12.1476 64.1285 11.8447C64.8614 11.5419 65.647 11.3873 66.44 11.39L66.42 11.43ZM66.42 21.43C67.2111 21.43 67.9845 21.1954 68.6423 20.7559C69.3001 20.3163 69.8128 19.6916 70.1155 18.9607C70.4183 18.2298 70.4975 17.4256 70.3431 16.6496C70.1888 15.8737 69.8078 15.161 69.2484 14.6016C68.689 14.0422 67.9763 13.6612 67.2004 13.5069C66.4244 13.3525 65.6202 13.4317 64.8893 13.7345C64.1584 14.0372 63.5336 14.5499 63.0941 15.2077C62.6546 15.8655 62.42 16.6389 62.42 17.43C62.4358 18.4839 62.8669 19.489 63.6197 20.2268C64.3724 20.9645 65.386 21.3754 66.44 21.37L66.42 21.43ZM62.42 25.37H70.42V27.37H62.42V25.37ZM74.55 11.39H76.55V27.29H74.55V11.39ZM79.32 11.39H81.32C81.423 11.3791 81.5269 11.3791 81.63 11.39C82.4676 11.2991 83.315 11.3857 84.1169 11.644C84.9188 11.9024 85.6574 12.3267 86.2844 12.8894C86.9115 13.4521 87.413 14.1406 87.7563 14.91C88.0997 15.6794 88.2771 16.5125 88.2771 17.355C88.2771 18.1975 88.0997 19.0306 87.7563 19.8C87.413 20.5694 86.9115 21.2579 86.2844 21.8206C85.6574 22.3833 84.9188 22.8076 84.1169 23.066C83.315 23.3243 82.4676 23.4109 81.63 23.32H81.32V27.32H79.32V11.39ZM81.32 13.39V21.3H81.63C82.1949 21.3752 82.7693 21.3289 83.3149 21.164C83.8604 20.9992 84.3644 20.7197 84.7931 20.3443C85.2219 19.9689 85.5654 19.5062 85.8008 18.9872C86.0362 18.4682 86.158 17.9049 86.158 17.335C86.158 16.7651 86.0362 16.2018 85.8008 15.6828C85.5654 15.1638 85.2219 14.7011 84.7931 14.3257C84.3644 13.9502 83.8604 13.6708 83.3149 13.5059C82.7693 13.3411 82.1949 13.2948 81.63 13.37C81.5211 13.3813 81.4137 13.4048 81.31 13.44L81.32 13.39ZM95.73 12.54L94.25 13.71C93.9947 13.4432 93.6685 13.2548 93.3098 13.167C92.9511 13.0792 92.5748 13.0956 92.2251 13.2143C91.8753 13.3329 91.5668 13.5489 91.3356 13.8369C91.1044 14.1249 90.9602 14.4729 90.92 14.84V15C90.92 15.88 91.53 16.47 92.72 16.55C97.3 16.83 99.4 18.98 99.4 21.82V22C99.2817 23.124 98.8431 24.1904 98.1363 25.0724C97.4295 25.9544 96.4842 26.6147 95.413 26.975C94.3417 27.3352 93.1895 27.3802 92.0934 27.1045C90.9973 26.8289 90.0034 26.2442 89.23 25.42L90.76 24.24C91.1161 24.6217 91.551 24.9213 92.0345 25.1182C92.518 25.315 93.0385 25.4044 93.56 25.38C94.5232 25.4308 95.4687 25.1075 96.1991 24.4776C96.9296 23.8478 97.3885 22.9601 97.48 22V21.86C97.48 19.19 94.86 18.7 92.59 18.48C90.49 18.28 88.98 16.97 88.98 15.08V15C89.054 14.016 89.5031 13.098 90.2344 12.4356C90.9657 11.7731 91.9235 11.4167 92.91 11.44C93.4328 11.4246 93.9529 11.5189 94.437 11.717C94.921 11.9151 95.3581 12.2125 95.72 12.59L95.73 12.54ZM107.23 25.26C109.72 25.26 111.69 22.57 111.69 19.26V11.26H113.69V19.26C113.69 23.66 110.81 27.21 107.27 27.21C103.73 27.21 100.85 23.66 100.85 19.26V11.26H102.85V19.26C102.77 22.62 104.74 25.31 107.22 25.31L107.23 25.26ZM129.04 27.26H127.04V17.36L122.43 23.36L117.82 17.36V27.29H115.82V11.39L122.42 20.08L129.02 11.39L129.04 27.26Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3Cpath d='M13.63 9C13.63 7.55722 13.0569 6.17353 12.0367 5.15334C11.0165 4.13314 9.63278 3.56 8.19 3.56C6.74722 3.56 5.36354 4.13314 4.34334 5.15334C3.32314 6.17353 2.75 7.55722 2.75 9V25.45L7.23 28.66V36.48H9.15V28.66L13.63 25.45V9ZM11.71 18.2L9.15 20.76V18.36L11.71 15.8V18.2ZM4.71 15.8L7.27 18.36V20.76L4.71 18.2V15.8ZM11.71 13.08L8.19 16.6L4.67 13V10.6L8.19 14.12L11.71 10.6V13.08ZM8.19 5.48C8.96415 5.48342 9.71583 5.74053 10.3299 6.21193C10.944 6.68333 11.3866 7.34303 11.59 8.09L8.19 11.48L4.79 8.09C4.98594 7.3356 5.42537 6.66695 6.04013 6.18781C6.65489 5.70866 7.41059 5.44579 8.19 5.43999V5.48ZM4.67 24.48V20.88L7.23 23.44V26.3L4.67 24.48ZM9.15 26.31V23.44L11.71 20.88V24.47L9.15 26.31Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-4' width='100' height='51' viewBox='0 0 100 51' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M2.58517 29.5165H5.41809V43.4072H2.58517V29.5165Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M7.06117 38.6479C7.0593 37.6502 7.35345 36.6743 7.9064 35.8438C8.45935 35.0133 9.24624 34.3655 10.1675 33.9824C11.0887 33.5993 12.1029 33.4981 13.0817 33.6916C14.0605 33.8851 14.9599 34.3646 15.666 35.0695C16.3722 35.7743 16.8534 36.6728 17.0487 37.6512C17.2441 38.6296 17.1448 39.644 16.7634 40.566C16.382 41.4879 15.7357 42.276 14.9062 42.8305C14.0768 43.3851 13.1015 43.681 12.1038 43.681C11.4402 43.6886 10.7819 43.5637 10.1673 43.3135C9.55272 43.0634 8.99423 42.6931 8.52459 42.2243C8.05495 41.7556 7.6836 41.1978 7.43231 40.5836C7.18102 39.9695 7.05484 39.3114 7.06117 38.6479ZM14.2945 38.6479C14.2834 38.2172 14.1455 37.7993 13.8981 37.4466C13.6507 37.0938 13.3048 36.8219 12.9036 36.6647C12.5024 36.5075 12.0638 36.4722 11.6427 36.563C11.2215 36.6538 10.8365 36.8668 10.5357 37.1753C10.235 37.4838 10.0319 37.8742 9.95184 38.2976C9.87179 38.7209 9.91837 39.1585 10.0857 39.5555C10.2531 39.9525 10.5338 40.2914 10.8927 40.5297C11.2517 40.768 11.6729 40.8952 12.1038 40.8953C12.3985 40.9036 12.6918 40.8507 12.9651 40.7399C13.2384 40.6291 13.4858 40.4629 13.6917 40.2517C13.8975 40.0405 14.0574 39.789 14.1611 39.513C14.2649 39.2369 14.3103 38.9424 14.2945 38.6479Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M28.5346 33.8886V42.935C28.5346 46.1362 26.0322 47.4866 23.5015 47.4866C22.6116 47.5528 21.7206 47.3728 20.9261 46.9664C20.1316 46.56 19.4643 45.9428 18.9972 45.1825L21.4335 43.7755C21.6268 44.1651 21.9327 44.4878 22.3115 44.7016C22.6903 44.9154 23.1246 45.0106 23.5582 44.9747C23.8434 45.0223 24.1358 45.0037 24.4128 44.9203C24.6898 44.837 24.9439 44.6912 25.1556 44.4941C25.3672 44.297 25.5308 44.0539 25.6337 43.7836C25.7366 43.5133 25.776 43.223 25.7489 42.935V42.0568C25.4159 42.4666 24.9909 42.7921 24.5086 43.007C24.0263 43.2219 23.5001 43.3202 22.9727 43.2939C21.6904 43.2939 20.4607 42.7845 19.5539 41.8778C18.6472 40.9711 18.1378 39.7413 18.1378 38.459C18.1378 37.1767 18.6472 35.947 19.5539 35.0403C20.4607 34.1336 21.6904 33.6242 22.9727 33.6242C23.4998 33.6001 24.0252 33.6994 24.5072 33.9141C24.9892 34.1289 25.4144 34.4532 25.7489 34.8612V33.9169L28.5346 33.8886ZM25.7489 38.459C25.7678 37.9998 25.6488 37.5454 25.4074 37.1542C25.1659 36.7631 24.813 36.4531 24.394 36.2642C23.975 36.0752 23.509 36.0159 23.056 36.0939C22.603 36.1718 22.1837 36.3835 21.852 36.7016C21.5202 37.0198 21.2912 37.4299 21.1944 37.8792C21.0975 38.3285 21.1373 38.7966 21.3086 39.2231C21.4799 39.6497 21.7748 40.0152 22.1555 40.2728C22.5362 40.5305 22.9852 40.6683 23.4448 40.6687C23.7449 40.6899 24.046 40.6481 24.3288 40.5458C24.6117 40.4435 24.87 40.2832 25.0871 40.075C25.3041 39.8668 25.4752 39.6154 25.5892 39.3371C25.7032 39.0588 25.7576 38.7597 25.7489 38.459Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M30.1683 38.6479C30.1664 37.6502 30.4606 36.6743 31.0135 35.8438C31.5665 35.0133 32.3534 34.3655 33.2746 33.9824C34.1958 33.5993 35.21 33.4981 36.1888 33.6916C37.1676 33.8851 38.067 34.3646 38.7732 35.0695C39.4793 35.7743 39.9605 36.6728 40.1559 37.6512C40.3512 38.6296 40.2519 39.644 39.8705 40.566C39.4891 41.4879 38.8428 42.276 38.0134 42.8305C37.1839 43.3851 36.2086 43.681 35.2109 43.681C34.5474 43.6886 33.889 43.5637 33.2744 43.3135C32.6598 43.0634 32.1013 42.6931 31.6317 42.2243C31.1621 41.7556 30.7907 41.1978 30.5394 40.5836C30.2881 39.9695 30.1619 39.3114 30.1683 38.6479ZM37.4017 38.6479C37.3905 38.2172 37.2526 37.7993 37.0052 37.4466C36.7578 37.0938 36.4119 36.8219 36.0107 36.6647C35.6096 36.5075 35.171 36.4722 34.7498 36.563C34.3286 36.6538 33.9436 36.8668 33.6428 37.1753C33.3421 37.4838 33.139 37.8742 33.0589 38.2976C32.9789 38.7209 33.0255 39.1585 33.1928 39.5555C33.3602 39.9525 33.6409 40.2914 33.9998 40.5297C34.3588 40.768 34.78 40.8952 35.2109 40.8953C35.5041 40.9009 35.7953 40.8461 36.0664 40.7341C36.3374 40.6221 36.5825 40.4555 36.7863 40.2446C36.9901 40.0338 37.1482 39.7831 37.2509 39.5084C37.3535 39.2337 37.3984 38.9407 37.3828 38.6479H37.4017Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M41.5661 31.339C41.5661 30.9991 41.6669 30.6668 41.8557 30.3842C42.0446 30.1016 42.313 29.8813 42.627 29.7512C42.9411 29.6211 43.2866 29.5871 43.62 29.6534C43.9534 29.7197 44.2596 29.8834 44.5 30.1237C44.7404 30.3641 44.904 30.6703 44.9703 31.0037C45.0367 31.3371 45.0026 31.6827 44.8726 31.9967C44.7425 32.3107 44.5222 32.5792 44.2396 32.768C43.9569 32.9568 43.6247 33.0576 43.2847 33.0576C42.8297 33.0552 42.394 32.8733 42.0722 32.5515C41.7504 32.2298 41.5686 31.7941 41.5661 31.339ZM41.8588 33.8886H44.6917V43.4072H41.8588V33.8886Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M57.0431 38.6479C57.0774 39.2771 56.987 39.9069 56.777 40.501C56.5669 41.0951 56.2415 41.6418 55.8193 42.1096C55.3971 42.5774 54.8866 42.9571 54.3171 43.2268C53.7476 43.4965 53.1304 43.6509 52.501 43.6811C51.9726 43.7064 51.445 43.6156 50.9556 43.4149C50.4661 43.2142 50.0266 42.9086 49.6681 42.5196V47.2411H46.8352V33.8886H49.6681V34.7857C50.0266 34.3967 50.4661 34.0911 50.9556 33.8904C51.445 33.6897 51.9726 33.5989 52.501 33.6242C53.1296 33.6544 53.746 33.8085 54.3148 34.0776C54.8837 34.3468 55.3938 34.7256 55.8158 35.1924C56.2379 35.6592 56.5635 36.2047 56.7741 36.7977C56.9848 37.3907 57.0762 38.0195 57.0431 38.6479ZM54.2102 38.6479C54.199 38.2047 54.058 37.7745 53.8047 37.4106C53.5514 37.0468 53.197 36.7651 52.7853 36.6007C52.3736 36.4362 51.9226 36.3961 51.4884 36.4854C51.0541 36.5746 50.6555 36.7893 50.342 37.1028C50.0285 37.4163 49.8139 37.8148 49.7246 38.2491C49.6354 38.6834 49.6755 39.1343 49.8399 39.546C50.0044 39.9577 50.286 40.3122 50.6499 40.5654C51.0138 40.8187 51.444 40.9597 51.8872 40.9709C52.1965 40.9906 52.5064 40.9438 52.7962 40.8338C53.0859 40.7237 53.3487 40.5529 53.567 40.3329C53.7852 40.1128 53.9539 39.8486 54.0616 39.558C54.1692 39.2674 54.2135 38.9571 54.1913 38.6479H54.2102Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M65.863 40.5554C65.863 42.7462 63.9744 43.681 61.8969 43.681C61.067 43.7545 60.2341 43.5779 59.5054 43.174C58.7768 42.7701 58.1856 42.1574 57.8081 41.4147L60.2822 40.0077C60.3826 40.3512 60.5976 40.65 60.8913 40.8544C61.1851 41.0588 61.5399 41.1566 61.8969 41.1314C62.5863 41.1314 62.9262 40.9142 62.9262 40.5365C62.9262 39.4883 58.2047 40.0455 58.2047 36.7593C58.2047 34.6818 59.9611 33.6336 61.9819 33.6336C62.7276 33.611 63.4658 33.7881 64.12 34.1468C64.7742 34.5054 65.3205 35.0325 65.7025 35.6733L63.219 36.9765C63.1093 36.7271 62.9295 36.5149 62.7015 36.3657C62.4735 36.2165 62.2072 36.1367 61.9347 36.136C61.4437 36.136 61.1415 36.3249 61.1415 36.6743C61.1793 37.7602 65.863 37.0331 65.863 40.5554Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M76.2881 33.8886V43.4072H73.4551V42.5196C73.1256 42.914 72.7074 43.2248 72.2347 43.4267C71.7621 43.6286 71.2483 43.7157 70.7355 43.6811C68.8469 43.6811 67.1755 42.3118 67.1755 39.7339V33.8886H70.0084V39.3184C69.9835 39.5498 70.0105 39.7838 70.0873 40.0035C70.1641 40.2232 70.2888 40.423 70.4525 40.5885C70.6161 40.754 70.8146 40.8809 71.0334 40.9601C71.2522 41.0394 71.486 41.0688 71.7176 41.0465C72.7564 41.0465 73.4835 40.4421 73.4835 39.0918V33.8886H76.2881Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M92.6623 37.5713V43.4071H89.8293V37.8169C89.8293 36.8726 89.3666 36.2493 88.4601 36.2493C87.5536 36.2493 86.9681 36.9198 86.9681 38.0435V43.4071H84.1352V37.8169C84.1352 36.8726 83.6819 36.2493 82.7659 36.2493C81.85 36.2493 81.2834 36.9198 81.2834 38.0435V43.4071H78.4505V33.8886H81.2834V34.7668C81.5795 34.3789 81.9678 34.0712 82.4131 33.8717C82.8584 33.6721 83.3465 33.587 83.833 33.6242C84.3216 33.6004 84.8081 33.7037 85.2449 33.9237C85.6818 34.1438 86.0542 34.4733 86.326 34.8801C86.642 34.4548 87.0607 34.1165 87.5429 33.8969C88.0251 33.6773 88.5551 33.5834 89.0833 33.6242C91.2364 33.6242 92.6623 35.1917 92.6623 37.5713Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M95.0798 33.832C96.248 33.832 97.195 32.8849 97.195 31.7167C97.195 30.5485 96.248 29.6015 95.0798 29.6015C93.9116 29.6015 92.9645 30.5485 92.9645 31.7167C92.9645 32.8849 93.9116 33.832 95.0798 33.832Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M34.6443 22.3115C40.1151 22.3115 44.55 17.8765 44.55 12.4057C44.55 6.93493 40.1151 2.49997 34.6443 2.49997C29.1735 2.49997 24.7385 6.93493 24.7385 12.4057C24.7385 17.8765 29.1735 22.3115 34.6443 22.3115Z' class='ccompli1' fill='%23394149'%3E%3C/path%3E%3Cpath d='M56.7882 22.3115C62.259 22.3115 66.6939 17.8765 66.6939 12.4057C66.6939 6.93493 62.259 2.49997 56.7882 2.49997C51.3174 2.49997 46.8824 6.93493 46.8824 12.4057C46.8824 17.8765 51.3174 22.3115 56.7882 22.3115Z' class='ccompli2' fill='%23394149'%3E%3C/path%3E%3Cpath d='M22.4061 2.49997H2.60406V22.302H22.4061V2.49997Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-4' width='100' height='51' viewBox='0 0 100 51' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M2.58517 29.5165H5.41809V43.4072H2.58517V29.5165Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M7.06117 38.6479C7.0593 37.6502 7.35345 36.6743 7.9064 35.8438C8.45935 35.0133 9.24624 34.3655 10.1675 33.9824C11.0887 33.5993 12.1029 33.4981 13.0817 33.6916C14.0605 33.8851 14.9599 34.3646 15.666 35.0695C16.3722 35.7743 16.8534 36.6728 17.0487 37.6512C17.2441 38.6296 17.1448 39.644 16.7634 40.566C16.382 41.4879 15.7357 42.276 14.9062 42.8305C14.0768 43.3851 13.1015 43.681 12.1038 43.681C11.4402 43.6886 10.7819 43.5637 10.1673 43.3135C9.55272 43.0634 8.99423 42.6931 8.52459 42.2243C8.05495 41.7556 7.6836 41.1978 7.43231 40.5836C7.18102 39.9695 7.05484 39.3114 7.06117 38.6479ZM14.2945 38.6479C14.2834 38.2172 14.1455 37.7993 13.8981 37.4466C13.6507 37.0938 13.3048 36.8219 12.9036 36.6647C12.5024 36.5075 12.0638 36.4722 11.6427 36.563C11.2215 36.6538 10.8365 36.8668 10.5357 37.1753C10.235 37.4838 10.0319 37.8742 9.95184 38.2976C9.87179 38.7209 9.91837 39.1585 10.0857 39.5555C10.2531 39.9525 10.5338 40.2914 10.8927 40.5297C11.2517 40.768 11.6729 40.8952 12.1038 40.8953C12.3985 40.9036 12.6918 40.8507 12.9651 40.7399C13.2384 40.6291 13.4858 40.4629 13.6917 40.2517C13.8975 40.0405 14.0574 39.789 14.1611 39.513C14.2649 39.2369 14.3103 38.9424 14.2945 38.6479Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M28.5346 33.8886V42.935C28.5346 46.1362 26.0322 47.4866 23.5015 47.4866C22.6116 47.5528 21.7206 47.3728 20.9261 46.9664C20.1316 46.56 19.4643 45.9428 18.9972 45.1825L21.4335 43.7755C21.6268 44.1651 21.9327 44.4878 22.3115 44.7016C22.6903 44.9154 23.1246 45.0106 23.5582 44.9747C23.8434 45.0223 24.1358 45.0037 24.4128 44.9203C24.6898 44.837 24.9439 44.6912 25.1556 44.4941C25.3672 44.297 25.5308 44.0539 25.6337 43.7836C25.7366 43.5133 25.776 43.223 25.7489 42.935V42.0568C25.4159 42.4666 24.9909 42.7921 24.5086 43.007C24.0263 43.2219 23.5001 43.3202 22.9727 43.2939C21.6904 43.2939 20.4607 42.7845 19.5539 41.8778C18.6472 40.9711 18.1378 39.7413 18.1378 38.459C18.1378 37.1767 18.6472 35.947 19.5539 35.0403C20.4607 34.1336 21.6904 33.6242 22.9727 33.6242C23.4998 33.6001 24.0252 33.6994 24.5072 33.9141C24.9892 34.1289 25.4144 34.4532 25.7489 34.8612V33.9169L28.5346 33.8886ZM25.7489 38.459C25.7678 37.9998 25.6488 37.5454 25.4074 37.1542C25.1659 36.7631 24.813 36.4531 24.394 36.2642C23.975 36.0752 23.509 36.0159 23.056 36.0939C22.603 36.1718 22.1837 36.3835 21.852 36.7016C21.5202 37.0198 21.2912 37.4299 21.1944 37.8792C21.0975 38.3285 21.1373 38.7966 21.3086 39.2231C21.4799 39.6497 21.7748 40.0152 22.1555 40.2728C22.5362 40.5305 22.9852 40.6683 23.4448 40.6687C23.7449 40.6899 24.046 40.6481 24.3288 40.5458C24.6117 40.4435 24.87 40.2832 25.0871 40.075C25.3041 39.8668 25.4752 39.6154 25.5892 39.3371C25.7032 39.0588 25.7576 38.7597 25.7489 38.459Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M30.1683 38.6479C30.1664 37.6502 30.4606 36.6743 31.0135 35.8438C31.5665 35.0133 32.3534 34.3655 33.2746 33.9824C34.1958 33.5993 35.21 33.4981 36.1888 33.6916C37.1676 33.8851 38.067 34.3646 38.7732 35.0695C39.4793 35.7743 39.9605 36.6728 40.1559 37.6512C40.3512 38.6296 40.2519 39.644 39.8705 40.566C39.4891 41.4879 38.8428 42.276 38.0134 42.8305C37.1839 43.3851 36.2086 43.681 35.2109 43.681C34.5474 43.6886 33.889 43.5637 33.2744 43.3135C32.6598 43.0634 32.1013 42.6931 31.6317 42.2243C31.1621 41.7556 30.7907 41.1978 30.5394 40.5836C30.2881 39.9695 30.1619 39.3114 30.1683 38.6479ZM37.4017 38.6479C37.3905 38.2172 37.2526 37.7993 37.0052 37.4466C36.7578 37.0938 36.4119 36.8219 36.0107 36.6647C35.6096 36.5075 35.171 36.4722 34.7498 36.563C34.3286 36.6538 33.9436 36.8668 33.6428 37.1753C33.3421 37.4838 33.139 37.8742 33.0589 38.2976C32.9789 38.7209 33.0255 39.1585 33.1928 39.5555C33.3602 39.9525 33.6409 40.2914 33.9998 40.5297C34.3588 40.768 34.78 40.8952 35.2109 40.8953C35.5041 40.9009 35.7953 40.8461 36.0664 40.7341C36.3374 40.6221 36.5825 40.4555 36.7863 40.2446C36.9901 40.0338 37.1482 39.7831 37.2509 39.5084C37.3535 39.2337 37.3984 38.9407 37.3828 38.6479H37.4017Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M41.5661 31.339C41.5661 30.9991 41.6669 30.6668 41.8557 30.3842C42.0446 30.1016 42.313 29.8813 42.627 29.7512C42.9411 29.6211 43.2866 29.5871 43.62 29.6534C43.9534 29.7197 44.2596 29.8834 44.5 30.1237C44.7404 30.3641 44.904 30.6703 44.9703 31.0037C45.0367 31.3371 45.0026 31.6827 44.8726 31.9967C44.7425 32.3107 44.5222 32.5792 44.2396 32.768C43.9569 32.9568 43.6247 33.0576 43.2847 33.0576C42.8297 33.0552 42.394 32.8733 42.0722 32.5515C41.7504 32.2298 41.5686 31.7941 41.5661 31.339ZM41.8588 33.8886H44.6917V43.4072H41.8588V33.8886Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M57.0431 38.6479C57.0774 39.2771 56.987 39.9069 56.777 40.501C56.5669 41.0951 56.2415 41.6418 55.8193 42.1096C55.3971 42.5774 54.8866 42.9571 54.3171 43.2268C53.7476 43.4965 53.1304 43.6509 52.501 43.6811C51.9726 43.7064 51.445 43.6156 50.9556 43.4149C50.4661 43.2142 50.0266 42.9086 49.6681 42.5196V47.2411H46.8352V33.8886H49.6681V34.7857C50.0266 34.3967 50.4661 34.0911 50.9556 33.8904C51.445 33.6897 51.9726 33.5989 52.501 33.6242C53.1296 33.6544 53.746 33.8085 54.3148 34.0776C54.8837 34.3468 55.3938 34.7256 55.8158 35.1924C56.2379 35.6592 56.5635 36.2047 56.7741 36.7977C56.9848 37.3907 57.0762 38.0195 57.0431 38.6479ZM54.2102 38.6479C54.199 38.2047 54.058 37.7745 53.8047 37.4106C53.5514 37.0468 53.197 36.7651 52.7853 36.6007C52.3736 36.4362 51.9226 36.3961 51.4884 36.4854C51.0541 36.5746 50.6555 36.7893 50.342 37.1028C50.0285 37.4163 49.8139 37.8148 49.7246 38.2491C49.6354 38.6834 49.6755 39.1343 49.8399 39.546C50.0044 39.9577 50.286 40.3122 50.6499 40.5654C51.0138 40.8187 51.444 40.9597 51.8872 40.9709C52.1965 40.9906 52.5064 40.9438 52.7962 40.8338C53.0859 40.7237 53.3487 40.5529 53.567 40.3329C53.7852 40.1128 53.9539 39.8486 54.0616 39.558C54.1692 39.2674 54.2135 38.9571 54.1913 38.6479H54.2102Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M65.863 40.5554C65.863 42.7462 63.9744 43.681 61.8969 43.681C61.067 43.7545 60.2341 43.5779 59.5054 43.174C58.7768 42.7701 58.1856 42.1574 57.8081 41.4147L60.2822 40.0077C60.3826 40.3512 60.5976 40.65 60.8913 40.8544C61.1851 41.0588 61.5399 41.1566 61.8969 41.1314C62.5863 41.1314 62.9262 40.9142 62.9262 40.5365C62.9262 39.4883 58.2047 40.0455 58.2047 36.7593C58.2047 34.6818 59.9611 33.6336 61.9819 33.6336C62.7276 33.611 63.4658 33.7881 64.12 34.1468C64.7742 34.5054 65.3205 35.0325 65.7025 35.6733L63.219 36.9765C63.1093 36.7271 62.9295 36.5149 62.7015 36.3657C62.4735 36.2165 62.2072 36.1367 61.9347 36.136C61.4437 36.136 61.1415 36.3249 61.1415 36.6743C61.1793 37.7602 65.863 37.0331 65.863 40.5554Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M76.2881 33.8886V43.4072H73.4551V42.5196C73.1256 42.914 72.7074 43.2248 72.2347 43.4267C71.7621 43.6286 71.2483 43.7157 70.7355 43.6811C68.8469 43.6811 67.1755 42.3118 67.1755 39.7339V33.8886H70.0084V39.3184C69.9835 39.5498 70.0105 39.7838 70.0873 40.0035C70.1641 40.2232 70.2888 40.423 70.4525 40.5885C70.6161 40.754 70.8146 40.8809 71.0334 40.9601C71.2522 41.0394 71.486 41.0688 71.7176 41.0465C72.7564 41.0465 73.4835 40.4421 73.4835 39.0918V33.8886H76.2881Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M92.6623 37.5713V43.4071H89.8293V37.8169C89.8293 36.8726 89.3666 36.2493 88.4601 36.2493C87.5536 36.2493 86.9681 36.9198 86.9681 38.0435V43.4071H84.1352V37.8169C84.1352 36.8726 83.6819 36.2493 82.7659 36.2493C81.85 36.2493 81.2834 36.9198 81.2834 38.0435V43.4071H78.4505V33.8886H81.2834V34.7668C81.5795 34.3789 81.9678 34.0712 82.4131 33.8717C82.8584 33.6721 83.3465 33.587 83.833 33.6242C84.3216 33.6004 84.8081 33.7037 85.2449 33.9237C85.6818 34.1438 86.0542 34.4733 86.326 34.8801C86.642 34.4548 87.0607 34.1165 87.5429 33.8969C88.0251 33.6773 88.5551 33.5834 89.0833 33.6242C91.2364 33.6242 92.6623 35.1917 92.6623 37.5713Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M95.0798 33.832C96.248 33.832 97.195 32.8849 97.195 31.7167C97.195 30.5485 96.248 29.6015 95.0798 29.6015C93.9116 29.6015 92.9645 30.5485 92.9645 31.7167C92.9645 32.8849 93.9116 33.832 95.0798 33.832Z' class='cneutral' fill='%23394149'%3E%3C/path%3E%3Cpath d='M34.6443 22.3115C40.1151 22.3115 44.55 17.8765 44.55 12.4057C44.55 6.93493 40.1151 2.49997 34.6443 2.49997C29.1735 2.49997 24.7385 6.93493 24.7385 12.4057C24.7385 17.8765 29.1735 22.3115 34.6443 22.3115Z' class='ccompli1' fill='%23394149'%3E%3C/path%3E%3Cpath d='M56.7882 22.3115C62.259 22.3115 66.6939 17.8765 66.6939 12.4057C66.6939 6.93493 62.259 2.49997 56.7882 2.49997C51.3174 2.49997 46.8824 6.93493 46.8824 12.4057C46.8824 17.8765 51.3174 22.3115 56.7882 22.3115Z' class='ccompli2' fill='%23394149'%3E%3C/path%3E%3Cpath d='M22.4061 2.49997H2.60406V22.302H22.4061V2.49997Z' class='ccustom' fill='%23394149'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					}
				],
				logo_size: "small"
			}
		});

	component_5 = new Component$6({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				}
			}
		});

	component_6 = new Component$7({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				},
				superhead: "Calendar infrastructure",
				heading: "All the features you need to connect with your customers.",
				subheading: "",
				teasers: [
					{
						"link": { "url": "/", "label": "Read more" },
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1499951360447-b19be8fe80f5?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2070&q=80",
							"url": "https://images.unsplash.com/photo-1499951360447-b19be8fe80f5?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2070&q=80",
							"size": null
						},
						"title": "Real-time collaboration",
						"content": {
							"html": "<p>Instant updates to your calendar without having to go through a third party app.</p>",
							"markdown": "Instant updates to your calendar without having to go through a third party app."
						}
					},
					{
						"link": { "url": "/", "label": "Learn More" },
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1521737852567-6949f3f9f2b5?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2047&q=80",
							"url": "https://images.unsplash.com/photo-1521737852567-6949f3f9f2b5?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2047&q=80",
							"size": null
						},
						"title": "Endless integrations",
						"content": {
							"html": "<p>Integrate your google calendar and any other third-party calendar. Everything in one place.</p>",
							"markdown": "Integrate your google calendar and any other third-party calendar. Everything in one place."
						}
					}
				]
			}
		});

	component_7 = new Component$8({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				},
				superhead: "Testiominals",
				heading: "Hear from our recent users",
				testimonials: [
					{
						"name": "Jess Jones",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1489424731084-a5d8b219a5bb?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxzZWFyY2h8MjZ8fHBvcnRyYWl0fGVufDB8fDB8fA%3D%3D&auto=format&fit=crop&w=800&q=60",
							"url": "https://images.unsplash.com/photo-1489424731084-a5d8b219a5bb?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxzZWFyY2h8MjZ8fHBvcnRyYWl0fGVufDB8fDB8fA%3D%3D&auto=format&fit=crop&w=800&q=60",
							"size": null
						},
						"quote": {
							"html": "<p>\"Incididunt ipsum elit Lorem Lorem do tempor adipisicing magna laboris labore nostrud magna cillum. Qui quis elit eu officia eu.\" </p>",
							"markdown": "\"Incididunt ipsum elit Lorem Lorem do tempor adipisicing magna laboris labore nostrud magna cillum. Qui quis elit eu officia eu.\" "
						},
						"subtitle": "Director at Expensify"
					},
					{
						"name": "Sal Lane",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1522075469751-3a6694fb2f61?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxzZWFyY2h8MjJ8fHBvcnRyYWl0fGVufDB8fDB8fA%3D%3D&auto=format&fit=crop&w=800&q=60",
							"url": "https://images.unsplash.com/photo-1522075469751-3a6694fb2f61?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxzZWFyY2h8MjJ8fHBvcnRyYWl0fGVufDB8fDB8fA%3D%3D&auto=format&fit=crop&w=800&q=60",
							"size": null
						},
						"quote": {
							"html": "<p>\"Proident ad mollit cupidatat enim consequat nisi laborum aliqua. Reprehenderit exercitation laboris consequat sunt occaecat magna sunt velit in occaecat.\" </p>",
							"markdown": "\"Proident ad mollit cupidatat enim consequat nisi laborum aliqua. Reprehenderit exercitation laboris consequat sunt occaecat magna sunt velit in occaecat.\" "
						},
						"subtitle": "Executive at Fintech"
					},
					{
						"name": "Laney Lee",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1597223557154-721c1cecc4b0?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=1180&q=80",
							"url": "https://images.unsplash.com/photo-1597223557154-721c1cecc4b0?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=1180&q=80",
							"size": null
						},
						"quote": {
							"html": "<p>\"Aute sint culpa Lorem ipsum mollit do cillum ullamco cupidatat cupidatat ipsum est. Consectetur id nisi pariatur velit qui.\" </p>",
							"markdown": "\"Aute sint culpa Lorem ipsum mollit do cillum ullamco cupidatat cupidatat ipsum est. Consectetur id nisi pariatur velit qui.\" "
						},
						"subtitle": "Developer at Apple"
					},
					{
						"name": "Henry Hue",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1552058544-f2b08422138a?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=798&q=80",
							"url": "https://images.unsplash.com/photo-1552058544-f2b08422138a?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=798&q=80",
							"size": null
						},
						"quote": {
							"html": "<p>\"Nulla esse commodo consectetur dolore exercitation culpa cillum elit. Lorem ut in sit irure tempor id tempor adipisicing labore enim veniam.\" </p>",
							"markdown": "\"Nulla esse commodo consectetur dolore exercitation culpa cillum elit. Lorem ut in sit irure tempor id tempor adipisicing labore enim veniam.\" "
						},
						"subtitle": "Designer at Media Agency"
					}
				]
			}
		});

	component_8 = new Component$9({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				},
				heading: "We're moving fast, signup for updates and more.",
				form: {
					"footer": "We'll send you bi-weekly emails about our new features.",
					"placeholder": "Your Email",
					"button_label": "Submit"
				},
				cards: [
					{
						"icon": "mdi:user-heart",
						"title": "User friendly & fun",
						"description": "With a clear intuitive interface, you can easily add and view events."
					},
					{
						"icon": "material-symbols:speed",
						"title": "Responsive and speedy",
						"description": "Our desktop and web application are both super speedy."
					}
				]
			}
		});

	component_9 = new Component$a({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				},
				footer_nav: [
					{
						"link": { "url": "/about", "label": "About us" }
					},
					{
						"link": { "url": "/why", "label": "Why Cali" }
					}
				],
				social: [
					{
						"icon": "mdi:twitter",
						"link": {
							"url": "https://twitter.com",
							"label": "Twitter"
						}
					},
					{
						"icon": "mdi:facebook",
						"link": {
							"url": "https://facebook.com",
							"label": "Facebook"
						}
					},
					{
						"icon": "mdi:github",
						"link": {
							"url": "https://github.com",
							"label": "Github"
						}
					}
				]
			}
		});

	component_10 = new Component$b({
			props: {
				favicon: {
					"alt": "",
					"src": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"url": "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png",
					"size": null
				}
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
			t7 = space();
			create_component(component_8.$$.fragment);
			t8 = space();
			create_component(component_9.$$.fragment);
			t9 = space();
			create_component(component_10.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
			t7 = claim_space(nodes);
			claim_component(component_8.$$.fragment, nodes);
			t8 = claim_space(nodes);
			claim_component(component_9.$$.fragment, nodes);
			t9 = claim_space(nodes);
			claim_component(component_10.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			insert_hydration(target, t7, anchor);
			mount_component(component_8, target, anchor);
			insert_hydration(target, t8, anchor);
			mount_component(component_9, target, anchor);
			insert_hydration(target, t9, anchor);
			mount_component(component_10, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			transition_in(component_8.$$.fragment, local);
			transition_in(component_9.$$.fragment, local);
			transition_in(component_10.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			transition_out(component_8.$$.fragment, local);
			transition_out(component_9.$$.fragment, local);
			transition_out(component_10.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
			if (detaching) detach(t7);
			destroy_component(component_8, detaching);
			if (detaching) detach(t8);
			destroy_component(component_9, detaching);
			if (detaching) detach(t9);
			destroy_component(component_10, detaching);
		}
	};
}

class Component$c extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$b, safe_not_equal, {});
	}
}

export default Component$c;
