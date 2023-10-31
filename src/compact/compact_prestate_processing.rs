//! Processing for the compact format as specified here: https://github.com/ledgerwatch/erigon/blob/devel/docs/programmers_guide/witness_formal_spec.md

use std::{
    any::type_name,
    collections::{linked_list::CursorMut, HashMap, LinkedList},
    error::Error,
    fmt::{self, Display},
    io::{Cursor, Read},
    iter,
};

use enum_as_inner::EnumAsInner;
use eth_trie_utils::{
    nibbles::{FromHexPrefixError, Nibbles},
    partial_trie::HashedPartialTrie,
};
use ethereum_types::{H256, U256};
use log::trace;
use serde::{de::DeserializeOwned, Deserialize};
use thiserror::Error;

use super::compact_to_partial_trie::{
    create_partial_trie_from_remaining_witness_elem, CompactToPartialOutput,
};
use crate::{
    trace_protocol::TrieCompact,
    types::{CodeHash, TrieRootHash},
};

pub type CompactParsingResult<T> = Result<T, CompactParsingError>;

type BranchMask = u32;

type Balance = U256;
type Nonce = U256;
type HasCode = bool;
type HasStorage = bool;

type HashValue = H256;
type RawValue = Vec<u8>;
type RawCode = Vec<u8>;

const MAX_WITNESS_ENTRIES_NEEDED_TO_MATCH_A_RULE: usize = 3;
const BRANCH_MAX_CHILDREN: usize = 16;

#[derive(Debug, Error)]
pub enum CompactParsingError {
    #[error("Missing header")]
    MissingHeader,

    #[error("Invalid opcode operator (\"{0:x}\")")]
    InvalidOperator(u8),

    #[error("Reached the end of the byte stream when we still expected more data")]
    UnexpectedEndOfStream,

    #[error("Unable to parse an expected byte vector (error: {0})")]
    InvalidByteVector(String),

    #[error("Unable to parse the type \"{0}\" from cbor bytes {1}")]
    InvalidBytesForType(&'static str, String, String),

    #[error("Invalid block witness entries: {0:?}")]
    InvalidWitnessFormat(Vec<WitnessEntry>),

    #[error("There were multiple entries remaining after the compact block witness was processed (Remaining entries: {0:#?})")]
    NonSingleEntryAfterProcessing(WitnessEntries),

    #[error("Branch mask {0:#b} stated there should be {1} preceding nodes but instead found {2} (nodes: {3:?})")]
    IncorrectNumberOfNodesPrecedingBranch(BranchMask, usize, usize, Vec<WitnessEntry>),

    #[error(
        "Expected a branch to have {0} preceding nodes but only had {1} (mask: {2}, nodes: {3:?})"
    )]
    MissingExpectedNodesPrecedingBranch(usize, usize, BranchMask, Vec<WitnessEntry>),

    #[error("Expected the entry preceding {0} positions behind a {1} entry to be a node but instead found a {2}. (nodes: {3:?})")]
    PrecedingNonNodeEntryFoundWhenProcessingRule(usize, &'static str, String, Vec<WitnessEntry>),

    #[error("Unable to create key nibbles from bytes {0}")]
    KeyError(#[from] FromHexPrefixError),
}

#[derive(Debug, enumn::N)]
enum Opcode {
    Leaf = 0x00,
    Extension = 0x01,
    Branch = 0x02,
    Hash = 0x03,
    Code = 0x04,
    AccountLeaf = 0x05,
    EmptyRoot = 0x06,
}

#[derive(Clone, Debug, EnumAsInner)]
pub enum WitnessEntry {
    Instruction(Instruction),
    Node(NodeEntry),
}

impl Display for WitnessEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WitnessEntry::Instruction(i) => write!(f, "Instruction({})", i),
            WitnessEntry::Node(n) => write!(f, "Node({})", n),
        }
    }
}

// TODO: Ignore `NEW_TRIE` for now...
#[derive(Clone, Debug, Eq, PartialEq)]
enum Instruction {
    Leaf(Nibbles, RawValue),
    Extension(Nibbles),
    Branch(BranchMask),
    Hash(HashValue),
    Code(RawCode),
    AccountLeaf(Nibbles, Nonce, Balance, HasCode, HasStorage),
    EmptyRoot,
}

impl Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Leaf(_, _) => write!(f, "Leaf"),
            Instruction::Extension(_) => write!(f, "Extension"),
            Instruction::Branch(_) => write!(f, "Branch"),
            Instruction::Hash(_) => write!(f, "Hash"),
            Instruction::Code(_) => write!(f, "Code"),
            Instruction::AccountLeaf(_, _, _, _, _) => write!(f, "AccountLeaf"),
            Instruction::EmptyRoot => write!(f, "EmptyRoot"),
        }
    }
}

impl From<NodeEntry> for WitnessEntry {
    fn from(v: NodeEntry) -> Self {
        WitnessEntry::Node(v)
    }
}

impl From<Instruction> for WitnessEntry {
    fn from(v: Instruction) -> Self {
        Self::Instruction(v)
    }
}

#[derive(Clone, Debug)]
pub(crate) enum NodeEntry {
    Branch([Option<Box<NodeEntry>>; 16]),
    Code(Vec<u8>),
    Empty,
    Hash(HashValue),
    Leaf(Nibbles, LeafNodeData),
    Extension(Nibbles, Box<NodeEntry>),
}

impl Display for NodeEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeEntry::Branch(_) => write!(f, "Branch"),
            NodeEntry::Code(_) => write!(f, "Code"),
            NodeEntry::Empty => write!(f, "Empty"),
            NodeEntry::Hash(_) => write!(f, "Hash"),
            NodeEntry::Leaf(_, _) => write!(f, "Leaf"),
            NodeEntry::Extension(_, _) => write!(f, "Extension"),
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct ValueNodeData(pub(super) Vec<u8>);

impl From<Vec<u8>> for ValueNodeData {
    fn from(v: Vec<u8>) -> Self {
        Self(v)
    }
}

#[derive(Clone, Debug)]
pub(super) enum LeafNodeData {
    Value(ValueNodeData),
    Account(AccountNodeData),
}

#[derive(Clone, Debug)]
pub(super) enum AccountNodeCode {
    CodeNode(Vec<u8>),
    HashNode(TrieRootHash),
}

#[derive(Clone, Debug)]
pub(super) struct AccountNodeData {
    pub(super) nonce: Nonce,
    pub(super) balance: Balance,
    pub(super) storage_root: Option<TrieRootHash>,
    pub(super) account_node_code: Option<AccountNodeCode>,
}

impl AccountNodeData {
    fn new(
        nonce: Nonce,
        balance: Balance,
        storage_root: Option<TrieRootHash>,
        account_node_code: Option<AccountNodeCode>,
    ) -> Self {
        Self {
            nonce,
            balance,
            storage_root,
            account_node_code,
        }
    }
}

#[derive(Debug, Deserialize)]
struct LeafData {
    key: Nibbles,
    value: Vec<u8>,
}

#[derive(Debug)]
pub(crate) struct Header {
    version: u8,
}

impl Display for Header {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Erigon block witness version {}", self.version)
    }
}

impl Header {
    pub(crate) fn version_is_compatible(&self, target_ver: u8) -> bool {
        self.version == target_ver
    }
}

#[derive(Debug)]
struct ParserState {
    entries: WitnessEntries,
}

impl ParserState {
    fn create_and_extract_header(
        witness_bytes_raw: Vec<u8>,
    ) -> CompactParsingResult<(Header, Self)> {
        let witness_bytes = WitnessBytes::new(witness_bytes_raw);
        let (header, entries) = witness_bytes.process_into_instructions_and_header()?;

        let p_state = Self { entries };

        Ok((header, p_state))
    }

    fn parse(mut self) -> CompactParsingResult<CompactToPartialOutput> {
        let mut entry_buf = Vec::new();

        loop {
            let num_rules_applied = self.apply_rules_to_witness_entries(&mut entry_buf)?;

            if num_rules_applied == 0 {
                break;
            }
        }

        match self.entries.len() {
            1 => create_partial_trie_from_remaining_witness_elem(self.entries.pop().unwrap()),
            _ => Err(CompactParsingError::NonSingleEntryAfterProcessing(
                self.entries,
            )),
        }
    }

    fn apply_rules_to_witness_entries(
        &mut self,
        entry_buf: &mut Vec<WitnessEntry>,
    ) -> CompactParsingResult<usize> {
        let mut traverser = self.entries.create_collapsable_traverser();

        let mut tot_rules_applied = 0;

        while !traverser.at_end() {
            let num_rules_applied = Self::try_apply_rules_to_curr_entry(&mut traverser, entry_buf)?;
            tot_rules_applied += num_rules_applied;

            if num_rules_applied == 0 {
                // Unable to apply rule at current position, so advance the traverser.
                traverser.advance();
            }
        }

        Ok(tot_rules_applied)
    }

    fn try_apply_rules_to_curr_entry(
        traverser: &mut CollapsableWitnessEntryTraverser,
        buf: &mut Vec<WitnessEntry>,
    ) -> CompactParsingResult<usize> {
        traverser.get_next_n_elems_into_buf(MAX_WITNESS_ENTRIES_NEEDED_TO_MATCH_A_RULE, buf);

        // TODO: There is a decent amount of code duplication with the matches and the
        // calls to `invalid_witness_err`. We should condense this...

        // TODO: These clones are really bad, but we will clean this up once it works.
        match buf[0].clone() {
            WitnessEntry::Instruction(Instruction::Hash(h)) => {
                Self::traverser_replace_prev_n_nodes_entry_helper(1, traverser, NodeEntry::Hash(h))
            }
            WitnessEntry::Instruction(Instruction::Leaf(k, v)) => {
                Self::traverser_replace_prev_n_nodes_entry_helper(
                    1,
                    traverser,
                    NodeEntry::Leaf(k, LeafNodeData::Value(v.clone().into())),
                )
            }
            WitnessEntry::Instruction(Instruction::Extension(k)) => {
                traverser.get_prev_n_elems_into_buf(1, buf);

                match buf[0].clone() {
                    WitnessEntry::Node(node) => Self::traverser_replace_prev_n_nodes_entry_helper(
                        2,
                        traverser,
                        NodeEntry::Extension(k, Box::new(node.clone())),
                    ),
                    _ => Self::invalid_witness_err(2, TraverserDirection::Backwards, traverser),
                }
            }
            WitnessEntry::Instruction(Instruction::Code(c)) => {
                Self::traverser_replace_prev_n_nodes_entry_helper(
                    1,
                    traverser,
                    NodeEntry::Code(c.clone()),
                )
            }
            WitnessEntry::Instruction(Instruction::AccountLeaf(k, n, b, has_code, has_storage)) => {
                let (n_nodes_to_replace, account_node_code, s_root) = match (has_code, has_storage)
                {
                    (false, false) => Self::match_account_leaf_no_code_and_no_storage(),
                    (false, true) => {
                        Self::match_account_leaf_no_code_but_has_storage(traverser, buf)
                    }
                    (true, false) => {
                        Self::match_account_leaf_has_code_but_no_storage(traverser, buf)
                    }
                    (true, true) => Self::match_account_leaf_has_code_and_storage(traverser, buf),
                }?;

                let account_leaf_data = AccountNodeData::new(n, b, s_root, account_node_code);
                let leaf_node = WitnessEntry::Node(NodeEntry::Leaf(
                    k,
                    LeafNodeData::Account(account_leaf_data),
                ));
                traverser.replace_prev_n_entries_with_single_entry(n_nodes_to_replace, leaf_node);

                Ok(1)
            }
            WitnessEntry::Instruction(Instruction::Branch(mask)) => {
                Self::process_branch_instr(traverser, buf, mask)
            }
            _ => Ok(0),
        }
    }

    fn process_branch_instr(
        traverser: &mut CollapsableWitnessEntryTraverser,
        buf: &mut Vec<WitnessEntry>,
        mask: BranchMask,
    ) -> CompactParsingResult<usize> {
        let expected_number_of_preceding_nodes = mask.count_ones() as usize;

        traverser.get_prev_n_elems_into_buf(expected_number_of_preceding_nodes, buf);
        let number_available_preceding_elems = buf.len();

        if buf.len() != expected_number_of_preceding_nodes {
            return Err(CompactParsingError::IncorrectNumberOfNodesPrecedingBranch(
                mask,
                expected_number_of_preceding_nodes,
                number_available_preceding_elems,
                buf.clone(),
            ));
        }

        let mut branch_nodes = Self::create_empty_branch_node_entry();
        let mut curr_traverser_node_idx = 0;

        for (i, branch_node) in branch_nodes
            .iter_mut()
            .enumerate()
            .take(BRANCH_MAX_CHILDREN)
        {
            if mask as usize & (1 << i) != 0 {
                let entry_to_check = &buf[buf.len() - 1 - curr_traverser_node_idx];
                let node_entry = try_get_node_entry_from_witness_entry(entry_to_check)
                    .ok_or_else(|| {
                        let n_entries_behind_cursor =
                            number_available_preceding_elems - curr_traverser_node_idx;

                        CompactParsingError::PrecedingNonNodeEntryFoundWhenProcessingRule(
                            n_entries_behind_cursor,
                            "Branch",
                            entry_to_check.to_string(),
                            buf.clone(),
                        )
                    })?
                    .clone();

                *branch_node = Some(Box::new(node_entry));
                curr_traverser_node_idx += 1;
            }
        }

        let number_of_nodes_traversed = curr_traverser_node_idx; // For readability.
        if curr_traverser_node_idx != buf.len() {
            return Err(CompactParsingError::MissingExpectedNodesPrecedingBranch(
                expected_number_of_preceding_nodes,
                number_of_nodes_traversed,
                mask,
                buf.clone(),
            ));
        }

        traverser.replace_prev_n_entries_with_single_entry(
            number_of_nodes_traversed + 1,
            NodeEntry::Branch(branch_nodes).into(),
        );
        Ok(1)
    }

    // ... Because we can't do `[None; 16]` without implementing `Copy`.
    fn create_empty_branch_node_entry() -> [Option<Box<NodeEntry>>; 16] {
        [
            None, None, None, None, None, None, None, None, None, None, None, None, None, None,
            None, None,
        ]
    }

    fn match_account_leaf_no_code_and_no_storage(
    ) -> CompactParsingResult<(usize, Option<AccountNodeCode>, Option<TrieRootHash>)> {
        Ok((0, None, None))
    }

    fn match_account_leaf_no_code_but_has_storage(
        traverser: &mut CollapsableWitnessEntryTraverser,
        buf: &mut Vec<WitnessEntry>,
    ) -> CompactParsingResult<(usize, Option<AccountNodeCode>, Option<TrieRootHash>)> {
        traverser.get_prev_n_elems_into_buf(1, buf);

        match buf[0].clone() {
            WitnessEntry::Node(node) => match Self::try_get_storage_hash_from_node(&node) {
                Some(s_hash) => Ok((1, None, Some(s_hash))),
                None => Self::invalid_witness_err(1, TraverserDirection::Backwards, traverser),
            },
            _ => Self::invalid_witness_err(2, TraverserDirection::Backwards, traverser),
        }
    }

    fn match_account_leaf_has_code_but_no_storage(
        traverser: &mut CollapsableWitnessEntryTraverser,
        buf: &mut Vec<WitnessEntry>,
    ) -> CompactParsingResult<(usize, Option<AccountNodeCode>, Option<TrieRootHash>)> {
        traverser.get_prev_n_elems_into_buf(1, buf);

        match buf[0].clone() {
            WitnessEntry::Node(NodeEntry::Code(code)) => {
                Ok((1, Some(AccountNodeCode::CodeNode(code.clone())), None))
            }
            WitnessEntry::Node(NodeEntry::Hash(h)) => {
                Ok((1, Some(AccountNodeCode::HashNode(h)), None))
            }
            _ => Self::invalid_witness_err(2, TraverserDirection::Backwards, traverser),
        }
    }

    fn match_account_leaf_has_code_and_storage(
        traverser: &mut CollapsableWitnessEntryTraverser,
        buf: &mut Vec<WitnessEntry>,
    ) -> CompactParsingResult<(usize, Option<AccountNodeCode>, Option<TrieRootHash>)> {
        traverser.get_prev_n_elems_into_buf(2, buf);

        match &buf[0..=1] {
            [WitnessEntry::Node(NodeEntry::Code(_c)), WitnessEntry::Node(_node)] => {
                todo!()
            }
            [WitnessEntry::Node(NodeEntry::Hash(_h)), WitnessEntry::Node(_node)] => {
                todo!()
            }
            _ => Self::invalid_witness_err(3, TraverserDirection::Backwards, traverser),
        }
    }

    fn try_get_storage_hash_from_node(_node: &NodeEntry) -> Option<TrieRootHash> {
        todo!()
    }

    fn invalid_witness_err<T>(
        n: usize,
        t_dir: TraverserDirection,
        traverser: &mut CollapsableWitnessEntryTraverser,
    ) -> CompactParsingResult<T> {
        let adjacent_elems_buf = match t_dir {
            TraverserDirection::Forwards => traverser.get_next_n_elems(n).cloned().collect(),
            TraverserDirection::Backwards => traverser.get_prev_n_elems(n).cloned().collect(),
            TraverserDirection::Both => {
                let prev_elems = traverser.get_prev_n_elems(n);
                let next_elems_including_curr = traverser.get_next_n_elems(n + 1);
                let prev_elems_vec: Vec<_> = prev_elems.collect();

                prev_elems_vec
                    .into_iter()
                    .chain(next_elems_including_curr)
                    .cloned()
                    .collect()
            }
        };

        Err(CompactParsingError::InvalidWitnessFormat(
            adjacent_elems_buf,
        ))
    }

    fn traverser_replace_prev_n_nodes_entry_helper(
        n: usize,
        traverser: &mut CollapsableWitnessEntryTraverser,
        entry: NodeEntry,
    ) -> CompactParsingResult<usize> {
        traverser.replace_prev_n_entries_with_single_entry(n, WitnessEntry::Node(entry));
        Ok(1)
    }
}

struct WitnessBytes {
    byte_cursor: CompactCursor,
    instrs: WitnessEntries,
}

impl WitnessBytes {
    fn new(witness_bytes: Vec<u8>) -> Self {
        Self {
            byte_cursor: CompactCursor::new(witness_bytes),
            instrs: WitnessEntries::default(),
        }
    }

    fn process_into_instructions_and_header(
        mut self,
    ) -> CompactParsingResult<(Header, WitnessEntries)> {
        let header = self.parse_header()?;

        loop {
            self.process_operator()?;

            if self.byte_cursor.at_eof() {
                break;
            }
        }

        Ok((header, self.instrs))
    }

    fn process_operator(&mut self) -> CompactParsingResult<()> {
        let opcode_byte = self.byte_cursor.read_byte()?;

        let opcode =
            Opcode::n(opcode_byte).ok_or(CompactParsingError::InvalidOperator(opcode_byte))?;

        trace!("Processed {:?} opcode", opcode);

        self.process_data_following_opcode(opcode)
    }

    fn process_data_following_opcode(&mut self, opcode: Opcode) -> CompactParsingResult<()> {
        match opcode {
            Opcode::Leaf => self.process_leaf(),
            Opcode::Extension => self.process_extension(),
            Opcode::Branch => self.process_branch(),
            Opcode::Hash => self.process_hash(),
            Opcode::Code => self.process_code(),
            Opcode::AccountLeaf => self.process_leaf(),
            Opcode::EmptyRoot => self.process_empty_root(),
        }
    }

    fn process_leaf(&mut self) -> CompactParsingResult<()> {
        let key = key_bytes_to_nibbles(&self.byte_cursor.read_cbor_byte_array_to_vec()?);
        let value_raw = self.byte_cursor.read_cbor_byte_array_to_vec()?;

        self.push_entry(Instruction::Leaf(key, value_raw));
        Ok(())
    }

    fn process_extension(&mut self) -> CompactParsingResult<()> {
        let key = key_bytes_to_nibbles(&self.byte_cursor.read_cbor_byte_array_to_vec()?);

        self.push_entry(Instruction::Extension(key));
        Ok(())
    }

    fn process_branch(&mut self) -> CompactParsingResult<()> {
        let mask = self.byte_cursor.read_t()?;

        self.push_entry(Instruction::Branch(mask));
        Ok(())
    }

    fn process_hash(&mut self) -> CompactParsingResult<()> {
        let hash = self.byte_cursor.read_t()?;

        self.push_entry(Instruction::Hash(hash));
        Ok(())
    }

    fn process_code(&mut self) -> CompactParsingResult<()> {
        let code = self.byte_cursor.read_t()?;

        self.push_entry(Instruction::Code(code));
        Ok(())
    }

    fn process_account_leaf(&mut self) -> CompactParsingResult<()> {
        let key = key_bytes_to_nibbles(&self.byte_cursor.read_cbor_byte_array_to_vec()?);
        let nonce = self.byte_cursor.read_t()?;
        let balance = self.byte_cursor.read_t()?;
        let has_code = self.byte_cursor.read_t()?;
        let has_storage = self.byte_cursor.read_t()?;

        self.push_entry(Instruction::AccountLeaf(
            key,
            nonce,
            balance,
            has_code,
            has_storage,
        ));

        Ok(())
    }

    fn process_empty_root(&mut self) -> CompactParsingResult<()> {
        self.push_entry(Instruction::EmptyRoot);
        Ok(())
    }

    fn push_entry(&mut self, instr: Instruction) {
        self.instrs.push(instr.into())
    }

    fn parse_header(&mut self) -> CompactParsingResult<Header> {
        let h_byte = self
            .byte_cursor
            .read_byte()
            .map_err(|_| CompactParsingError::MissingHeader)?;

        Ok(Header { version: h_byte })
    }
}

#[derive(Debug)]
struct CompactCursor {
    intern: Cursor<Vec<u8>>,
    temp_buf: Vec<u8>,
}

impl CompactCursor {
    fn new(bytes: Vec<u8>) -> Self {
        Self {
            intern: Cursor::new(bytes),
            temp_buf: Vec::default(),
        }
    }

    fn read_t<T: DeserializeOwned>(&mut self) -> CompactParsingResult<T> {
        let starting_pos = self.intern.position();

        ciborium::from_reader(&mut self.intern).map_err(move |err| {
            let ending_pos = self.intern.position();
            let type_bytes = self.intern.clone().into_inner()
                [starting_pos as usize..ending_pos as usize]
                .to_vec();
            let type_bytes_hex = hex::encode(type_bytes);

            CompactParsingError::InvalidBytesForType(
                type_name::<T>(),
                type_bytes_hex,
                err.to_string(),
            )
        })
    }

    fn read_byte(&mut self) -> CompactParsingResult<u8> {
        let mut single_byte_buf = [0];

        // Assume this is always caused by hitting the end of the stream?
        self.intern
            .read_exact(&mut single_byte_buf)
            .map_err(|_err| CompactParsingError::UnexpectedEndOfStream)?;

        Ok(single_byte_buf[0])
    }

    // I don't think it's possible to not read to a vec here with `ciborium`... In
    // theory this should be doable, but the way the library I don't think we can.
    fn read_cbor_byte_array_to_vec(&mut self) -> CompactParsingResult<Vec<u8>> {
        Self::ciborium_byte_vec_err_reader_res_to_parsing_res(ciborium::from_reader(
            &mut self.intern,
        ))
    }

    fn ciborium_byte_vec_err_reader_res_to_parsing_res<T, E: Error>(
        res: Result<T, E>,
    ) -> CompactParsingResult<T> {
        res.map_err(|err| CompactParsingError::InvalidByteVector(err.to_string()))
    }

    fn at_eof(&self) -> bool {
        self.intern.position() as usize == self.intern.get_ref().len()
    }
}

/// We kind of want a wrapper around the actual data structure I think since
/// there's a good chance this will change a few times in the future.
#[derive(Debug, Default)]
pub struct WitnessEntries {
    // Yeah a LL is actually (unfortunately) a very good choice here. We will be doing a ton of
    // inserts mid-list, and the list can get very large. There might be a better choice for a data
    // structure, but for now, this will make performance not scale exponentially with list
    // size.
    intern: LinkedList<WitnessEntry>,
}

impl WitnessEntries {
    fn push(&mut self, entry: WitnessEntry) {
        self.intern.push_back(entry)
    }

    fn pop(&mut self) -> Option<WitnessEntry> {
        self.intern.pop_back()
    }

    fn create_collapsable_traverser(&mut self) -> CollapsableWitnessEntryTraverser {
        let entry_cursor = self.intern.cursor_front_mut();

        CollapsableWitnessEntryTraverser { entry_cursor }
    }

    fn len(&self) -> usize {
        self.intern.len()
    }
}

// It's not quite an iterator, so this is the next best name that I can come up
// with.
#[derive(Debug)]
struct CollapsableWitnessEntryTraverser<'a> {
    entry_cursor: CursorMut<'a, WitnessEntry>,
}

// TODO: For now, lets just use pure values in the buffer, but we probably want
// to switch over to references later...
impl<'a> CollapsableWitnessEntryTraverser<'a> {
    fn advance(&mut self) {
        self.entry_cursor.move_next();
    }

    fn get_curr_elem(&self) -> Option<&WitnessEntry> {
        self.entry_cursor.as_cursor().current()
    }

    fn get_next_n_elems(&self, n: usize) -> impl Iterator<Item = &WitnessEntry> {
        let mut read_only_cursor = self.entry_cursor.as_cursor();

        iter::from_fn(move || {
            // Index returns a `None` if we are at the end of the LL.
            read_only_cursor.index().map(|_| {
                let entry = read_only_cursor.current();
                read_only_cursor.move_next();
                entry
            })
        })
        .flatten()
        .take(n)
    }

    fn get_prev_n_elems(&self, n: usize) -> impl Iterator<Item = &WitnessEntry> {
        let mut read_only_cursor = self.entry_cursor.as_cursor();

        iter::from_fn(move || {
            read_only_cursor.index().map(|_| {
                read_only_cursor.move_prev();
                read_only_cursor.current()
            })
        })
        .flatten()
        .take(n)
    }

    /// Get the previous `n` elements into a buf. Note that this does not
    /// include the element that we are currently pointing to.
    fn get_prev_n_elems_into_buf(&self, n: usize, buf: &mut Vec<WitnessEntry>) {
        buf.clear();
        buf.extend(self.get_prev_n_elems(n).cloned())
    }

    /// Get the next `n` elements into a buf. Note that this includes the
    /// element that we are currently pointing to.
    fn get_next_n_elems_into_buf(&self, n: usize, buf: &mut Vec<WitnessEntry>) {
        buf.clear();
        buf.extend(self.get_next_n_elems(n).cloned());
    }

    // Inclusive.
    fn replace_next_n_entries_with_single_entry(&mut self, n: usize, entry: WitnessEntry) {
        for _ in 0..n {
            self.entry_cursor.remove_current();
        }

        self.entry_cursor.insert_after(entry)
    }

    // Inclusive.
    fn replace_prev_n_entries_with_single_entry(&mut self, n: usize, entry: WitnessEntry) {
        for _ in 0..n {
            self.entry_cursor.remove_current();
            self.entry_cursor.move_prev();

            if self.entry_cursor.index().is_none() {
                break;
            }
        }
        self.entry_cursor.insert_after(entry);

        self.entry_cursor.move_next();
    }

    fn at_end(&self) -> bool {
        self.entry_cursor.as_cursor().current().is_none()
    }
}

fn try_get_node_entry_from_witness_entry(entry: &WitnessEntry) -> Option<&NodeEntry> {
    match entry {
        WitnessEntry::Node(n_entry) => Some(n_entry),
        _ => None,
    }
}

#[derive(Debug)]
enum TraverserDirection {
    Forwards,
    Backwards,
    Both,
}

pub(crate) fn process_compact_prestate(
    state: TrieCompact,
) -> CompactParsingResult<(
    Header,
    HashedPartialTrie,
    Option<HashMap<CodeHash, Vec<u8>>>,
)> {
    let (header, parser) = ParserState::create_and_extract_header(state.bytes)?;
    let out = parser.parse()?;

    let extra_code_hash_mappings = (!out.code.is_empty()).then_some(out.code);

    Ok((header, out.trie, extra_code_hash_mappings))
}

// TODO: Move behind a feature flag just used for debugging (but probably not
// `debug`)...
fn parse_just_to_instructions(bytes: Vec<u8>) -> CompactParsingResult<Vec<Instruction>> {
    let witness_bytes = WitnessBytes::new(bytes);
    let (_, entries) = witness_bytes.process_into_instructions_and_header()?;

    Ok(entries
        .intern
        .into_iter()
        .map(|entry| match entry {
            WitnessEntry::Instruction(instr) => instr,
            _ => unreachable!(
                "Found a non-instruction at a stage when we should only have instructions!"
            ),
        })
        .collect())
}

// TODO: This could probably be made a bit faster...
fn key_bytes_to_nibbles(bytes: &[u8]) -> Nibbles {
    let mut key = Nibbles::default();

    // I have no idea why Erigon is doing this with their keys, as I'm don't think
    // this is part of the yellow paper at all?
    let is_just_term_byte = bytes.len() == 1 && bytes[0] == 0x10;
    if is_just_term_byte {
        return key;
    }

    let flags = bytes[0];
    let is_odd = (flags & 0b00000001) != 0;
    let has_term = (flags & 0b00000010) != 0;

    // ... Term bit seems to have no effect on the key?
    let actual_key_bytes = match has_term {
        false => &bytes[1..],
        true => &bytes[1..],
    };

    if actual_key_bytes.is_empty() || is_just_term_byte {
        return key;
    }

    let final_byte_idx = actual_key_bytes.len() - 1;

    // The compact key format is kind of weird. We need to read the nibbles
    // backwards from how we expect it internally.
    for byte in &actual_key_bytes[..(final_byte_idx)] {
        let high_nib = (byte & 0b11110000) >> 4;
        let low_nib = byte & 0b00001111;

        key.push_nibble_back(high_nib);
        key.push_nibble_back(low_nib);
    }

    // The final byte we might need to ignore the last nibble, so we need to do it
    // separately.
    let final_byte = actual_key_bytes[final_byte_idx];
    let high_nib = (final_byte & 0b11110000) >> 4;
    key.push_nibble_back(high_nib);

    if !is_odd {
        let low_nib = final_byte & 0b00001111;
        key.push_nibble_back(low_nib);
    }

    key
}

#[cfg(test)]
mod tests {
    use eth_trie_utils::{nibbles::Nibbles, partial_trie::PartialTrie};

    use super::{key_bytes_to_nibbles, parse_just_to_instructions, Instruction};
    use crate::compact::{
        compact_prestate_processing::ParserState,
        complex_test_payloads::{TEST_PAYLOAD_1, TEST_PAYLOAD_2, TEST_PAYLOAD_3},
    };

    const SIMPLE_PAYLOAD_STR: &str = "01004110443132333400411044313233340218300042035044313233350218180158200000000000000000000000000000000000000000000000000000000000000012";

    fn init() {
        let _ = pretty_env_logger::try_init();
    }

    fn h_decode_key(h_bytes: &str) -> Nibbles {
        let bytes = hex::decode(h_bytes).unwrap();
        key_bytes_to_nibbles(&bytes)
    }

    fn h_decode(b_str: &str) -> Vec<u8> {
        hex::decode(b_str).unwrap()
    }

    #[test]
    fn simple_full() {
        init();

        let bytes = hex::decode(SIMPLE_PAYLOAD_STR).unwrap();
        let (header, parser) = ParserState::create_and_extract_header(bytes).unwrap();

        assert_eq!(header.version, 1);
        let _output = match parser.parse() {
            Ok(trie) => trie,
            Err(err) => panic!("{}", err),
        };
    }

    #[test]
    fn simple_instructions_are_parsed_correctly() {
        init();

        let bytes = hex::decode(SIMPLE_PAYLOAD_STR).unwrap();
        let instrs = parse_just_to_instructions(bytes);

        let instrs = match instrs {
            Ok(x) => x,
            Err(err) => panic!("{}", err),
        };

        let expected_instrs = vec![
            Instruction::Leaf(h_decode_key("10"), h_decode("31323334")),
            Instruction::Leaf(h_decode_key("10"), h_decode("31323334")),
            Instruction::Branch(0b00110000),
            Instruction::Leaf(h_decode_key("0350"), h_decode("31323335")),
            Instruction::Branch(0b00011000),
            Instruction::Extension(h_decode_key(
                "0000000000000000000000000000000000000000000000000000000000000012",
            )),
        ];

        for (i, expected_instr) in expected_instrs.into_iter().enumerate() {
            assert_eq!(expected_instr, instrs[i])
        }
    }

    #[test]
    fn complex_payload_1() {
        TEST_PAYLOAD_1.parse_and_check_hash_matches();
    }

    #[test]
    fn complex_payload_2() {
        TEST_PAYLOAD_2.parse_and_check_hash_matches();
    }

    #[test]
    fn complex_payload_3() {
        TEST_PAYLOAD_3.parse_and_check_hash_matches();
    }
}