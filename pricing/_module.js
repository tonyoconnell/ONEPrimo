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
			attr(div2, "id", "section-6b61dad7");
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

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i];
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].item;
	child_ctx[9] = list[i].icon;
	return child_ctx;
}

// (124:12) {#each tier.features as { item, icon }}
function create_each_block_1$1(ctx) {
	let li;
	let span0;
	let icon;
	let t0;
	let span1;
	let t1_value = /*item*/ ctx[8] + "";
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
			span1 = claim_element(li_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t1 = claim_text(span1_nodes, t1_value);
			span1_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "icon svelte-xdid9t");
			attr(span1, "class", "item svelte-xdid9t");
			attr(li, "class", "svelte-xdid9t");
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
			if (dirty & /*tiers*/ 8) icon_changes.icon = /*icon*/ ctx[9];
			icon.$set(icon_changes);
			if ((!current || dirty & /*tiers*/ 8) && t1_value !== (t1_value = /*item*/ ctx[8] + "")) set_data(t1, t1_value);
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

// (133:10) {#if tier.link.label}
function create_if_block$2(ctx) {
	let a;
	let t_value = /*tier*/ ctx[5].link.label + "";
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
			attr(a, "href", a_href_value = /*tier*/ ctx[5].link.url);
			attr(a, "class", "button svelte-xdid9t");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*tiers*/ 8 && t_value !== (t_value = /*tier*/ ctx[5].link.label + "")) set_data(t, t_value);

			if (dirty & /*tiers*/ 8 && a_href_value !== (a_href_value = /*tier*/ ctx[5].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (112:6) {#each tiers as tier}
function create_each_block$1(ctx) {
	let div1;
	let header;
	let div0;
	let span0;
	let t0_value = /*tier*/ ctx[5].price.numerator + "";
	let t0;
	let t1;
	let span1;
	let t2_value = /*tier*/ ctx[5].price.denominator + "";
	let t2;
	let t3;
	let h3;
	let t4_value = /*tier*/ ctx[5].title + "";
	let t4;
	let t5;
	let span2;
	let raw_value = /*tier*/ ctx[5].description.html + "";
	let t6;
	let hr;
	let t7;
	let ul;
	let t8;
	let t9;
	let current;
	let each_value_1 = /*tier*/ ctx[5].features;
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	let if_block = /*tier*/ ctx[5].link.label && create_if_block$2(ctx);

	return {
		c() {
			div1 = element("div");
			header = element("header");
			div0 = element("div");
			span0 = element("span");
			t0 = text(t0_value);
			t1 = space();
			span1 = element("span");
			t2 = text(t2_value);
			t3 = space();
			h3 = element("h3");
			t4 = text(t4_value);
			t5 = space();
			span2 = element("span");
			t6 = space();
			hr = element("hr");
			t7 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t8 = space();
			if (if_block) if_block.c();
			t9 = space();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			header = claim_element(div1_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span0 = claim_element(div0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t0 = claim_text(span0_nodes, t0_value);
			span0_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			span1 = claim_element(div0_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t2 = claim_text(span1_nodes, t2_value);
			span1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			h3 = claim_element(header_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t4 = claim_text(h3_nodes, t4_value);
			h3_nodes.forEach(detach);
			t5 = claim_space(header_nodes);
			span2 = claim_element(header_nodes, "SPAN", { class: true });
			var span2_nodes = children(span2);
			span2_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t6 = claim_space(div1_nodes);
			hr = claim_element(div1_nodes, "HR", { class: true });
			t7 = claim_space(div1_nodes);
			ul = claim_element(div1_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t8 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			t9 = claim_space(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "numerator svelte-xdid9t");
			attr(span1, "class", "denominator svelte-xdid9t");
			attr(div0, "class", "price svelte-xdid9t");
			attr(h3, "class", "title svelte-xdid9t");
			attr(span2, "class", "description svelte-xdid9t");
			attr(header, "class", "svelte-xdid9t");
			attr(hr, "class", "svelte-xdid9t");
			attr(ul, "class", "features svelte-xdid9t");
			attr(div1, "class", "tier svelte-xdid9t");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, header);
			append_hydration(header, div0);
			append_hydration(div0, span0);
			append_hydration(span0, t0);
			append_hydration(div0, t1);
			append_hydration(div0, span1);
			append_hydration(span1, t2);
			append_hydration(header, t3);
			append_hydration(header, h3);
			append_hydration(h3, t4);
			append_hydration(header, t5);
			append_hydration(header, span2);
			span2.innerHTML = raw_value;
			append_hydration(div1, t6);
			append_hydration(div1, hr);
			append_hydration(div1, t7);
			append_hydration(div1, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(div1, t8);
			if (if_block) if_block.m(div1, null);
			append_hydration(div1, t9);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*tiers*/ 8) && t0_value !== (t0_value = /*tier*/ ctx[5].price.numerator + "")) set_data(t0, t0_value);
			if ((!current || dirty & /*tiers*/ 8) && t2_value !== (t2_value = /*tier*/ ctx[5].price.denominator + "")) set_data(t2, t2_value);
			if ((!current || dirty & /*tiers*/ 8) && t4_value !== (t4_value = /*tier*/ ctx[5].title + "")) set_data(t4, t4_value);
			if ((!current || dirty & /*tiers*/ 8) && raw_value !== (raw_value = /*tier*/ ctx[5].description.html + "")) span2.innerHTML = raw_value;
			if (dirty & /*tiers*/ 8) {
				each_value_1 = /*tier*/ ctx[5].features;
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block_1$1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (/*tier*/ ctx[5].link.label) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$2(ctx);
					if_block.c();
					if_block.m(div1, t9);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
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
			destroy_each(each_blocks, detaching);
			if (if_block) if_block.d();
		}
	};
}

function create_fragment$3(ctx) {
	let div3;
	let section;
	let div2;
	let div0;
	let span;
	let t0;
	let t1;
	let h2;
	let t2;
	let t3;
	let h3;
	let t4;
	let t5;
	let div1;
	let current;
	let each_value = /*tiers*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			div0 = element("div");
			span = element("span");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h2 = element("h2");
			t2 = text(/*heading*/ ctx[1]);
			t3 = space();
			h3 = element("h3");
			t4 = text(/*subheading*/ ctx[2]);
			t5 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
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
			t3 = claim_space(div0_nodes);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t4 = claim_text(h3_nodes, /*subheading*/ ctx[2]);
			h3_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(div2_nodes);
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
			attr(span, "class", "superhead");
			attr(h2, "class", "heading");
			attr(h3, "class", "subheading svelte-xdid9t");
			attr(div0, "class", "heading-group");
			attr(div1, "class", "tiers svelte-xdid9t");
			attr(div2, "class", "section-container svelte-xdid9t");
			attr(section, "class", "svelte-xdid9t");
			attr(div3, "class", "section");
			attr(div3, "id", "section-3c4616ea");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, div0);
			append_hydration(div0, span);
			append_hydration(span, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h2);
			append_hydration(h2, t2);
			append_hydration(div0, t3);
			append_hydration(div0, h3);
			append_hydration(h3, t4);
			append_hydration(div2, t5);
			append_hydration(div2, div1);

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

			if (dirty & /*tiers*/ 8) {
				each_value = /*tiers*/ ctx[3];
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

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { superhead } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { tiers } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(2, subheading = $$props.subheading);
		if ('tiers' in $$props) $$invalidate(3, tiers = $$props.tiers);
	};

	return [superhead, heading, subheading, tiers, favicon];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 4,
			superhead: 0,
			heading: 1,
			subheading: 2,
			tiers: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i].icon;
	child_ctx[5] = list[i].title;
	child_ctx[6] = list[i].description;
	return child_ctx;
}

// (120:6) {#each cards as { icon, title, description }}
function create_each_block$2(ctx) {
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

function create_fragment$4(ctx) {
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
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
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
			attr(div3, "id", "section-7db88dc2");
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
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
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

function instance$4($$self, $$props, $$invalidate) {
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

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			favicon: 3,
			heading: 0,
			form: 1,
			cards: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$3(ctx, list, i) {
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
function create_each_block$3(ctx) {
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

function create_fragment$5(ctx) {
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
		each_blocks[i] = create_each_block$3(get_each_context$3(ctx, each_value, i));
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
			attr(div1, "id", "section-2e502921");
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
					const child_ctx = get_each_context$3(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$3(child_ctx);
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

function instance$5($$self, $$props, $$invalidate) {
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

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$5, create_fragment$5, safe_not_equal, { favicon: 2, footer_nav: 0, social: 1 });
	}
}

/* generated by Svelte v3.58.0 */

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
		init(this, options, instance$6, null, safe_not_equal, { favicon: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$6(ctx) {
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
				superhead: "pricing",
				heading: "There's a plan for everyone.",
				subheading: "Whether you just need to spin up a few projects or you want to take it to the next level. We have a plan for you.",
				tiers: [
					{
						"link": { "url": "/", "label": "Get Started" },
						"price": {
							"numerator": "$15",
							"denominator": "/month"
						},
						"title": "Individual",
						"features": [
							{
								"icon": "mdi:check",
								"item": "Asido saslt donet"
							},
							{
								"icon": "mdi:check",
								"item": "Aute magna occaecat"
							}
						],
						"description": {
							"html": "<p>Perfect for freelancers</p>",
							"markdown": "Perfect for freelancers\n\n"
						}
					},
					{
						"link": { "url": "/", "label": "Get Started" },
						"price": {
							"numerator": "$25",
							"denominator": "/month"
						},
						"title": "Business",
						"features": [
							{
								"icon": "mdi:check",
								"item": "Pariatur consectetur excepteur"
							},
							{
								"icon": "mdi:check",
								"item": "Lorem labore cupidatat"
							}
						],
						"description": {
							"html": "<p>Ullamco veniam id occaecat ullamco nisi et ipsum in ut velit reprehenderit nisi enim sunt. Elit eu commodo elit excepteur aute sit sit laborum.</p>",
							"markdown": "Ullamco veniam id occaecat ullamco nisi et ipsum in ut velit reprehenderit nisi enim sunt. Elit eu commodo elit excepteur aute sit sit laborum.\n\n"
						}
					},
					{
						"link": { "url": "/", "label": "Get Started" },
						"price": {
							"numerator": "$49",
							"denominator": "/month"
						},
						"title": "Premium",
						"features": [
							{
								"icon": "mdi:check",
								"item": "Sint fugiat magna"
							},
							{
								"icon": "mdi:check",
								"item": "Aute ad id"
							}
						],
						"description": {
							"html": "<p>Commodo irure ad duis nulla anim incididunt. Aute aute laboris qui tempor pariatur duis labore minim deserunt id laboris tempor sit aliquip adipisicing.</p>",
							"markdown": "Commodo irure ad duis nulla anim incididunt. Aute aute laboris qui tempor pariatur duis labore minim deserunt id laboris tempor sit aliquip adipisicing.\n\n"
						}
					}
				]
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
				heading: "Want to schedule a demo?",
				form: {
					"footer": "Submit your email and we'll be in touch to set up a zoom demo call.",
					"placeholder": "Your Email",
					"button_label": "Submit"
				},
				cards: [
					{
						"icon": "mdi:chat",
						"title": "24/7 Customer Service",
						"description": "Veniam laboris consectetur"
					},
					{
						"icon": "mdi:github",
						"title": "Open Source and Free",
						"description": "Never get locked in."
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
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
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
		}
	};
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$6, safe_not_equal, {});
	}
}

export default Component$7;
