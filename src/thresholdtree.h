// Copyright (c) 2015 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_THRESHOLDTREE_H
#define BITCOIN_THRESHOLDTREE_H

#include <stdlib.h>
#include <stdint.h>
#include <vector>

/** A generic iterator over threshold trees.
 *
 *  A threshold tree is a tree structure that describes a set of combinations
 *  of leaves.
 *  Every inner node defines a requirement that K (the threshold) of its
 *  N subnodes are satisfied. When K=1, it is equivalent to an OR over the N
 *  children. When K=N, it is equivalent to an AND over the N children.
 *
 *  The tree node data type should support the following methods:
 *  - bool Node::IsLeaf(): return whether a node is a leaf
 *  - int Node::Threshold(): return the threshold of a node (only for non-leaf
 *                           nodes)
 *  - int Node::Children(): return the number of children of a node (only for
 *                          non-leaf nodes).
 *  - Node* Node::Child(int pos): return a pointer to the pos'th child node
 *                                (only for non-leaf nodes).
 *
 *  An iterator is also parametrized in the type of an accumulator. This
 *  accumulator is an object kept inside the iterator, and matching leaves are
 *  added and removed from it. When a iterator reaches a stable combination,
 *  the accumulator can be queried to retrieve information about the matching
 *  subset of leaves. Using an accumulator means that early checks can be
 *  performed, and not all combinations are necessarily actually ever stored.
 */
template<typename Node, typename Accumulator>
class ThresholdTreeIterator {
    // InnerIterators are created for iterating over the combinations of one
    // node of the original tree.
    struct InnerIterator {
        Node* node; // Tree node this InnerIterator iterates over
        struct InnerChild {
            int position; // What position we're at (subnode iterates over node->children[position])
            InnerIterator* inner_iterator; // Inner iterator for the child.
        };
        std::vector<InnerChild> children;
    };

    // InnerIterator objects are cached and reused to avoid frequent allocation
    // within the iteration code.
    std::vector<InnerIterator*> all_inner_iterators;
    std::vector<InnerIterator*> available_inner_iterators;
    InnerIterator* iterator_root;
    Accumulator accumulator;

    // Return a new InnerIterator object (in unknown state).
    InnerIterator* AcquireInnerIterator() {
        if (!available_inner_iterators.empty()) {
            InnerIterator* ret = available_inner_iterators.back();
            available_inner_iterators.pop_back();
            return ret;
        }
        InnerIterator* ret = new InnerIterator();
        all_inner_iterators.push_back(ret);
        return ret;
    }

    // Return an InnerIterator object to the cache.
    void ReleaseInnerIterator(InnerIterator* iter) {
        available_inner_iterators.push_back(iter);
    }

    // Construct an InnerIterator object for a particular tree node.
    InnerIterator* BuildInnerIterator(Node* node) {
        InnerIterator *ret = AcquireInnerIterator();
        ret->node = node;
        if (node->IsLeaf()) {
            accumulator.Push(node);
            return ret;
        }
        int threshold = node->Threshold();
        ret->children.resize(threshold);
        for (int childnum = 0; childnum < threshold; childnum++) {
            ret->children[childnum].position = childnum;
            ret->children[childnum].inner_iterator = BuildInnerIterator(node->Child(childnum));
        }
        return ret;
    }

    // Move an InnerIterator to the next combinations it or its children allow.
    // This will return false if there are no combinations left. In that case,
    // InnerIterator will have been released.
    bool IncrementInnerIterator(InnerIterator* iter) {
        // First deal with the leaf case.
        if (iter->node->IsLeaf()) {
            accumulator.Pop(iter->node);
            ReleaseInnerIterator(iter);
            return false;
        }
        // Try to increment its child iterators first.
        for (int childnum = iter->children.size() - 1; childnum >= 0; childnum--) {
            if (IncrementInnerIterator(iter->children[childnum].inner_iterator)) {
                for (int childnum2 = childnum + 1; childnum2 < iter->children.size(); childnum2++) {
                    iter->children[childnum2].inner_iterator = BuildInnerIterator(iter->node->Child(iter->children[childnum2].position));
                }
                return true;
            }
        }
        // If we reach this point, all child InnerIterators have been exhausted and released, so
        // check quickly whether we're done entirely, in which case we can release this one as
        // well. Otherwise we will need to consturct new child InnerIterators for all positions.
        if (iter->children[0].position + iter->children.size() == iter->node->Children()) {
            ReleaseInnerIterator(iter);
            return false;
        }
        // If not, move to the next combinations of children.
        for (int childnum = iter->children.size() - 1; ; childnum--) {
            if (iter->children[childnum].position + iter->children.size() != childnum + iter->node->Children()) {
                iter->children[childnum].position++;
                for (int childnum2 = childnum + 1; childnum2 < iter->children.size(); childnum2++) {
                    iter->children[childnum2].position = iter->children[childnum2 - 1].position + 1;
                }
                for (int childnum2 = 0; childnum2 < iter->children.size(); childnum2++) {
                    iter->children[childnum2].inner_iterator = BuildInnerIterator(iter->node->Child(iter->children[childnum2].position));
                }
                return true;
            }
        }
    }

public:
    // Construct an iterator for a tree, using the empty constructor for the accumulator.
    ThresholdTreeIterator(Node* root) {
        iterator_root = BuildInnerIterator(root);
    }

    // Construct an iterator for a tree, constructing the accumulator with one argument.
    template<typename A>
    ThresholdTreeIterator(Node* root, const A& acc) : accumulator(acc) {
        iterator_root = BuildInnerIterator(root);
    }

    // Destroy an iterator and all its inner iterators.
    ~ThresholdTreeIterator() {
        for (typename std::vector<InnerIterator*>::iterator it = all_inner_iterators.begin(); it != all_inner_iterators.end(); it++) {
            delete *it;
        }
    }

    // Retrieve a pointer to the accumulator.
    Accumulator* GetAccumulator() {
        return &accumulator;
    }

    // Retrieve a pointer to the accumulator (const)
    const Accumulator* GetAccumulator() const {
        return &accumulator;
    }

    // Check whether this iterator is done iterating.
    bool Valid() const {
        return iterator_root != NULL;
    }

    // Move to the next combination.
    void Increment() {
        if (iterator_root && !IncrementInnerIterator(iterator_root)) {
            iterator_root = NULL;
        }
    }
};

// Compute the number of combinations, given the number of combinations allowed by children.
static inline uint64_t CountCombinationsFromArray(uint32_t pick, std::vector<uint64_t>::const_iterator begin, size_t total) {
    if (pick == 0) return 1;
    if (pick > total) return 0;
    uint64_t ret = 0;
    for (uint32_t pos = 0; pos <= total - pick; pos++) {
         ret += *(begin + pos) * CountCombinationsFromArray(pick - 1, begin + pos + 1, total - pos - 1);
    }
    return ret;
}

// Compute the number of combinations allowed by a threshold tree.
template<typename Node>
static inline uint64_t CountCombinations(Node* node) {
    if (node->IsLeaf()) return 1;
    std::vector<uint64_t> list;
    list.resize(node->Children());
    for (size_t pos = 0; pos < list.size(); pos++) {
        list[pos] = CountCombinations(node->Child(pos));
    }
    return CountCombinationsFromArray(node->Threshold(), list.begin(), list.size());
}

#endif
