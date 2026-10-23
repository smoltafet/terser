/***********************************************************************

  A JavaScript tokenizer / parser / beautifier / compressor.
  https://github.com/mishoo/UglifyJS2

  -------------------------------- (C) ---------------------------------

                           Author: Mihai Bazon
                         <mihai.bazon@gmail.com>
                       http://mihai.bazon.net/blog

  Distributed under the BSD license:

    Copyright 2012 (c) Mihai Bazon <mihai.bazon@gmail.com>

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

        * Redistributions of source code must retain the above
          copyright notice, this list of conditions and the following
          disclaimer.

        * Redistributions in binary form must reproduce the above
          copyright notice, this list of conditions and the following
          disclaimer in the documentation and/or other materials
          provided with the distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER “AS IS” AND ANY
    EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
    IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
    PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE
    LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
    OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
    PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
    PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
    THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
    TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
    THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
    SUCH DAMAGE.

 ***********************************************************************/

import {
    AST_Accessor,
    AST_Array,
    AST_Arrow,
    AST_Assign,
    AST_Binary,
    AST_Call,
    AST_Chain,
    AST_Class,
    AST_ClassPrivateProperty,
    AST_ClassProperty,
    AST_ClassStaticBlock,
    AST_ConciseMethod,
    AST_Conditional,
    AST_Constant,
    AST_DefClass,
    AST_Dot,
    AST_DynamicImport,
    AST_Expansion,
    AST_Function,
    AST_Lambda,
    AST_Node,
    AST_Number,
    AST_Object,
    AST_ObjectGetter,
    AST_ObjectKeyVal,
    AST_ObjectProperty,
    AST_ObjectSetter,
    AST_PrivateGetter,
    AST_PrivateSetter,
    AST_PrivateMethod,
    AST_PropAccess,
    AST_Scope,
    AST_Sequence,
    AST_SimpleStatement,
    AST_Sub,
    AST_SymbolClass,
    AST_SymbolConst,
    AST_SymbolLet,
    AST_SymbolRef,
    AST_SymbolUsing,
    AST_TemplateSegment,
    AST_TemplateString,
    AST_This,
    AST_Unary,
    AST_VarDef,
    TreeWalker,
} from "../ast.js";
import { make_node, return_null, return_this } from "../utils/index.js";
import { first_in_statement } from "../utils/first_in_statement.js";

import { pure_prop_access_globals } from "./native-objects.js";
import { lazy_op, unary_side_effects, is_nullish_shortcircuited } from "./inference.js";
import { WRITE_ONLY, set_flag, clear_flag } from "./compressor-flags.js";
import { make_sequence, is_func_expr, is_iife_call } from "./common.js";

// AST_Node#drop_side_effect_free() gets called when we don't care about the value,
// only about side effects. We'll be defining this method for each node type in this module
//
// Examples:
// foo++ -> foo++
// 1 + func() -> func()
// 10 -> (nothing)
// knownPureFunc(foo++) -> foo++

function def_drop_side_effect_free(node_or_nodes, func) {
    for (const node of [].concat(node_or_nodes)) {
        node.DEFMETHOD("drop_side_effect_free", func);
    }
}

// Drop side-effect-free elements from an array of expressions.
// Returns an array of expressions with side-effects or null
// if all elements were dropped. Note: original array may be
// returned if nothing changed.
function trim(nodes, compressor, first_in_statement) {
    var len = nodes.length;
    if (!len)  return null;

    var ret = [], changed = false;
    for (var i = 0; i < len; i++) {
        var node = nodes[i].drop_side_effect_free(compressor, first_in_statement);
        changed |= node !== nodes[i];
        if (node) {
            ret.push(node);
            first_in_statement = false;
        }
    }
    return changed ? ret.length ? ret : null : nodes;
}

def_drop_side_effect_free(AST_Node, return_this);
def_drop_side_effect_free(AST_Constant, return_null);
def_drop_side_effect_free(AST_This, return_null);

def_drop_side_effect_free(AST_Call, function (compressor, first_in_statement) {
    if (is_nullish_shortcircuited(this, compressor)) {
        return this.expression.drop_side_effect_free(compressor, first_in_statement);
    }

    if (!this.is_callee_pure(compressor)) {
        if (this.expression.is_call_pure(compressor)) {
            var exprs = this.args.slice();
            exprs.unshift(this.expression.expression);
            exprs = trim(exprs, compressor, first_in_statement);
            return exprs && make_sequence(this, exprs);
        }
        if (is_func_expr(this.expression)
            && (!this.expression.name || !this.expression.name.definition().references.length)) {
            var node = this.clone();
            node.expression.process_expression(false, compressor);
            return node;
        }
        return this;
    }

    var args = trim(this.args, compressor, first_in_statement);
    return args && make_sequence(this, args);
});

def_drop_side_effect_free(AST_DynamicImport, function (compressor, first_in_statement) {
    if (this.phase !== "source") return this;
    var args = trim(this.args, compressor, first_in_statement);
    return args && make_sequence(this, args);
});

def_drop_side_effect_free(AST_Accessor, return_null);

def_drop_side_effect_free(AST_Function, return_null);

def_drop_side_effect_free(AST_Arrow, return_null);

def_drop_side_effect_free(AST_Class, function (compressor) {
    const with_effects = [];

    if (this.is_self_referential() && this.has_side_effects(compressor)) {
        return this;
    }

    const trimmed_extends = this.extends && this.extends.drop_side_effect_free(compressor);
    if (trimmed_extends) with_effects.push(trimmed_extends);

    for (const prop of this.properties) {
        if (prop instanceof AST_ClassStaticBlock) {
            if (prop.has_side_effects(compressor)) {
                return this; // Be cautious about these
            }
        } else {
            const trimmed_prop = prop.drop_side_effect_free(compressor);
            if (trimmed_prop) with_effects.push(trimmed_prop);
        }
    }

    if (!with_effects.length)
        return null;

    const exprs = make_sequence(this, with_effects);
    if (this instanceof AST_DefClass) {
        // We want a statement
        return make_node(AST_SimpleStatement, this, { body: exprs });
    } else {
        return exprs;
    }
});

def_drop_side_effect_free([
    AST_ClassProperty,
    AST_ClassPrivateProperty,
], function (compressor) {
    const key = this.computed_key() && this.key.drop_side_effect_free(compressor);

    const value = this.static && this.value
        && this.value.drop_side_effect_free(compressor);

    if (key && value)
        return make_sequence(this, [key, value]);
    return key || value || null;
});

def_drop_side_effect_free(AST_Binary, function (compressor, first_in_statement) {
    var right = this.right.drop_side_effect_free(compressor);
    if (!right)
        return this.left.drop_side_effect_free(compressor, first_in_statement);
    if (lazy_op.has(this.operator)) {
        if (right === this.right)
            return this;
        var node = this.clone();
        node.right = right;
        return node;
    } else {
        var left = this.left.drop_side_effect_free(compressor, first_in_statement);
        if (!left)
            return this.right.drop_side_effect_free(compressor, first_in_statement);
        return make_sequence(this, [left, right]);
    }
});

def_drop_side_effect_free(AST_Assign, function (compressor) {
    if (this.logical)
        return this;

    var left = this.left;
    if (left.has_side_effects(compressor)
        || compressor.has_directive("use strict")
        && left instanceof AST_PropAccess
        && left.expression.is_constant()) {
        return this;
    }
    set_flag(this, WRITE_ONLY);
    while (left instanceof AST_PropAccess) {
        left = left.expression;
    }
    if (left.is_constant_expression(compressor.find_parent(AST_Scope))) {
        return this.right.drop_side_effect_free(compressor);
    }
    return this;
});

def_drop_side_effect_free(AST_Conditional, function (compressor) {
    var consequent = this.consequent.drop_side_effect_free(compressor);
    var alternative = this.alternative.drop_side_effect_free(compressor);
    if (consequent === this.consequent && alternative === this.alternative)
        return this;
    if (!consequent)
        return alternative ? make_node(AST_Binary, this, {
            operator: "||",
            left: this.condition,
            right: alternative
        }) : this.condition.drop_side_effect_free(compressor);
    if (!alternative)
        return make_node(AST_Binary, this, {
            operator: "&&",
            left: this.condition,
            right: consequent
        });
    var node = this.clone();
    node.consequent = consequent;
    node.alternative = alternative;
    return node;
});

def_drop_side_effect_free(AST_Unary, function (compressor, first_in_statement) {
    if (unary_side_effects.has(this.operator)) {
        if (!this.expression.has_side_effects(compressor)) {
            set_flag(this, WRITE_ONLY);
        } else {
            clear_flag(this, WRITE_ONLY);
        }
        return this;
    }
    if (this.operator == "typeof" && this.expression instanceof AST_SymbolRef)
        return null;
    var expression = this.expression.drop_side_effect_free(compressor, first_in_statement);
    if (first_in_statement && expression && is_iife_call(expression)) {
        if (expression === this.expression && this.operator == "!")
            return this;
        return expression.negate(compressor, first_in_statement);
    }
    return expression;
});

// Reading a variable is normally free of side effects, but a read in the
// variable's temporal dead zone throws a ReferenceError, and that throw
// must be preserved.  Returns true when this reference provably executes
// before the binding it resolves to is initialized:
//
// - a reference to a class's own name from the parts of the class
//   definition that are evaluated before the name is bound (the
//   extends clause and computed property keys);
// - a reference to a let/const/using binding from its own initializer,
//   or lexically before its declaration in the same file.  A lexical
//   binding's dead zone follows the program's statement order (hoisting
//   only ever moves execution earlier), so a reference that precedes
//   its declaration in the source may execute before the declaration
//   has run, while one that follows it in a position to resolve to the
//   same binding is only reachable after initialization.
function is_tdz_reference(ref, compressor) {
    var def = ref.definition();
    if (!def) return false;
    var is_class_name = def.orig.some(function(sym) {
        return sym instanceof AST_SymbolClass
            || sym.TYPE == "SymbolDefClass";
    });
    if (!is_class_name) {
        var is_lexical = def.orig[0] instanceof AST_SymbolLet
            || def.orig[0] instanceof AST_SymbolConst
            || def.orig[0] instanceof AST_SymbolUsing;
        if (!is_lexical) return false;
        // A reference from the declaration's own initializer is always
        // in the dead zone, even though it lexically follows the name.
        for (var k = 0, anc; anc = compressor.parent(k); k++) {
            if (anc instanceof AST_VarDef
                && (anc.name instanceof AST_SymbolLet
                    || anc.name instanceof AST_SymbolConst
                    || anc.name instanceof AST_SymbolUsing)
                && anc.name.definition() === def) {
                return true;
            }
            if (anc instanceof AST_Lambda) break;
        }
        var ref_start = ref.start;
        var def_start = def.orig[0].start;
        if (!!ref_start && !!def_start
            && ref_start.pos != null && def_start.pos != null
            && ref_start.file === def_start.file
            && ref_start.pos < def_start.pos) {
            return true;
        }
        // The ancestor walk above only sees the declaration when the
        // optimizer's walker is positioned over it; a drop may also be
        // requested for a whole subtree from elsewhere (e.g. dead-code
        // elimination at the toplevel).  Fall back to locating the
        // declaration below the node currently being optimized and
        // checking whether the reference lies in its initializer.
        var in_init = false;
        compressor.self().walk(new TreeWalker(function(node) {
            if (in_init) return true;
            if (node instanceof AST_VarDef
                && node.value
                && (node.name instanceof AST_SymbolLet
                    || node.name instanceof AST_SymbolConst
                    || node.name instanceof AST_SymbolUsing)
                && node.name.definition() === def) {
                node.value.walk(new TreeWalker(function(inner) {
                    // Match by position as well as by identity: the
                    // subtree being searched may be a clone of the one
                    // the reference belongs to.
                    if (inner === ref
                        || inner instanceof AST_SymbolRef
                        && inner.name === ref.name
                        && inner.start && ref.start
                        && inner.start.pos === ref.start.pos
                        && inner.start.file === ref.start.file) {
                        return (in_init = true);
                    }
                }));
                return true;
            }
        }));
        return in_init;
    }

    // Walk the ancestors of the node currently being optimized.  `child`
    // is the ancestor directly below `node` on that path, and `sub` the
    // one below `child`; together they show how the reference is reached.
    var child = compressor.self();
    var sub = null;
    for (var i = 0, node; node = compressor.parent(i); i++) {
        if (node instanceof AST_Class || node instanceof AST_DefClass) {
            if (node.name
                && node.name.definition()
                && node.name.definition() === def) {
                if (child === node.extends) return true;
                if (child instanceof AST_ObjectProperty) {
                    // Only the member's key is in the dead zone: computed
                    // keys are evaluated while the class is being defined,
                    // before its name is bound.  Everything else (method
                    // bodies, instance and static field initializers,
                    // static blocks) runs after the name is initialized.
                    if (sub === null || sub === child.key) return true;
                }
            }
            // The reference is not in this class's dead zone (or the
            // class is not the one being named); either way the class's
            // deferred parts run after the name is initialized.
            return false;
        }
        if (node instanceof AST_Lambda) return false;
        sub = child;
        child = node;
    }
    return false;
}

def_drop_side_effect_free(AST_SymbolRef, function (compressor) {
    const safe_access = this.is_declared(compressor)
        || pure_prop_access_globals.has(this.name);
    if (!safe_access) return this;
    if (is_tdz_reference(this, compressor)) return this;
    return null;
});

def_drop_side_effect_free(AST_Object, function (compressor, first_in_statement) {
    var values = trim(this.properties, compressor, first_in_statement);
    return values && make_sequence(this, values);
});

def_drop_side_effect_free(AST_ObjectKeyVal, function (compressor, first_in_statement) {
    const computed_key = this.key instanceof AST_Node;
    const key = computed_key && this.key.drop_side_effect_free(compressor, first_in_statement);
    const value = this.value.drop_side_effect_free(compressor, first_in_statement);
    if (key && value) {
        return make_sequence(this, [key, value]);
    }
    return key || value;
});

def_drop_side_effect_free([
    AST_ConciseMethod,
    AST_ObjectGetter,
    AST_ObjectSetter,
], function (compressor, first_in_statement) {
    return this.computed_key() ? this.key.drop_side_effect_free(compressor, first_in_statement) : null;
});

def_drop_side_effect_free([
    AST_PrivateMethod,
    AST_PrivateGetter,
    AST_PrivateSetter,
], function () {
    return null;
});

def_drop_side_effect_free(AST_Array, function (compressor, first_in_statement) {
    var values = trim(this.elements, compressor, first_in_statement);
    return values && make_sequence(this, values);
});

def_drop_side_effect_free(AST_Dot, function (compressor, first_in_statement) {
    if (is_nullish_shortcircuited(this, compressor)) {
        return this.expression.drop_side_effect_free(compressor, first_in_statement);
    }
    if (!this.optional && this.expression.may_throw_on_access(compressor)) {
        return this;
    }

    return this.expression.drop_side_effect_free(compressor, first_in_statement);
});

def_drop_side_effect_free(AST_Sub, function (compressor, first_in_statement) {
    if (is_nullish_shortcircuited(this, compressor)) {
        return this.expression.drop_side_effect_free(compressor, first_in_statement);
    }
    if (!this.optional && this.expression.may_throw_on_access(compressor)) {
        return this;
    }

    var property = this.property.drop_side_effect_free(compressor);
    if (property && this.optional) return this;

    var expression = this.expression.drop_side_effect_free(compressor, first_in_statement);

    if (expression && property) return make_sequence(this, [expression, property]);
    return expression || property;
});

def_drop_side_effect_free(AST_Chain, function (compressor, first_in_statement) {
    return this.expression.drop_side_effect_free(compressor, first_in_statement);
});

def_drop_side_effect_free(AST_Sequence, function (compressor) {
    var last = this.tail_node();
    var expr = last.drop_side_effect_free(compressor);
    if (expr === last)
        return this;
    var expressions = this.expressions.slice(0, -1);
    if (expr)
        expressions.push(expr);
    if (!expressions.length) {
        return make_node(AST_Number, this, { value: 0 });
    }
    return make_sequence(this, expressions);
});

def_drop_side_effect_free(AST_Expansion, function (compressor, first_in_statement) {
    return this.expression.drop_side_effect_free(compressor, first_in_statement);
});

def_drop_side_effect_free(AST_TemplateSegment, return_null);

def_drop_side_effect_free(AST_TemplateString, function (compressor) {
    var values = trim(this.segments, compressor, first_in_statement);
    return values && make_sequence(this, values);
});
