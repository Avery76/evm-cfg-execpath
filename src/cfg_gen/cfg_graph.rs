use crate::cfg_gen::dasm::*; 
use itertools::Itertools; //里面有很多方便的集合操作，比如排序、分组等。
use lazy_static::lazy_static; //可以让我们定义一些“全局变量”，只初始化一次，后面都能用。
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
};
use petgraph::prelude::GraphMap;
use petgraph::Direction;
use petgraph::Directed;

use super::BLOCK_ENDERS_U8;

lazy_static! {
    pub static ref TOKYO_NIGHT_COLORS: HashMap<&'static str, &'static str> = {
        let mut m = HashMap::new();
        m.insert("red", "#f7768e");
        m.insert("orange", "#ff9e64");
        m.insert("yellow", "#e0af68");
        m.insert("green", "#9ece6a");
        m.insert("cyan", "#73daca");
        m.insert("teal", "#2ac3de");
        m.insert("darkblue", "#7aa2f7");
        m.insert("purple", "#bb9af7");
        m.insert("bg", "#1a1b26");
        m.insert("font", "#c0caf5");
        m.insert("deepred", "#703440");
        m
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Edges {
    Jump,           // Next instruction in sequence
    ConditionTrue,  // Conditional jumpi, true branch
    ConditionFalse, // Conditional jumpi, false branch
    SymbolicJump,   // Jump to a symbolic value
} //定义了控制流图里“边”的几种类型

impl Debug for Edges {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Edges::Jump => write!(f, ""),
            Edges::ConditionTrue => write!(f, "True"),
            Edges::ConditionFalse => write!(f, "False"),
            Edges::SymbolicJump => write!(f, "Symbolic"),
        }
    }
} // 定义了每种边在打印时怎么显示。

type CFGDag = GraphMap<(u16, u16), Edges, Directed>; // 定义了一个有向图类型 CFGDag

pub struct CFGRunner<'a> {
    pub cfg_dag: CFGDag,
    pub last_node: Option<(u16, u16)>,
    pub jumpi_edge: Option<Edges>, // 记录最后一个节点和 jumpi 边的类型
    // 这两个字段用于跟踪 CFG 的状态
    pub bytecode: Vec<u8>, // 存储整个合约的字节码
    pub map_to_instructionblock: &'a mut BTreeMap<(u16, u16), InstructionBlock>, // 这个映射将 (start_pc, end_pc) 映射到指令块
    pub executed_pcs: Option<HashSet<u16>>, // 新增：记录执行过的PC
} // 定义了 CFGRunner 结构体，它包含了控制流图的 DAG、最后一个节点、jumpi 边、字节码和指令块的映射。

impl<'main> CFGRunner<'main> {
    pub fn new( // 构造函数，接受字节码和指令块的映射
        bytecode: Vec<u8>, 
        map_to_instructionblock: &'main mut BTreeMap<(u16, u16), InstructionBlock>, // 传入字节码和指令块的映射
    ) -> Self { // 返回一个新的 CFGRunner 实例
        // 初始化控制流图
        let mut cfg_dag: CFGDag = GraphMap::new(); // 创建一个新的控制流图

        for keys in map_to_instructionblock
            .keys() // 遍历指令块的键
            .sorted_by(|a, b| a.0.cmp(&b.0)) // 按照 start_pc 排序
        {
            cfg_dag.add_node(*keys); // 将每个 (start_pc, end_pc) 节点添加到图中
        } // 将所有的 (start_pc, end_pc) 节点添加到图中

        Self {
            cfg_dag,
            last_node: None, // 最后一个节点初始化为 None
            jumpi_edge: None,
            bytecode,
            map_to_instructionblock,
            executed_pcs: None, // 新增字段初始化为 None
        } // 返回一个新的 CFGRunner 实例
    }

    pub fn initialize_cfg_with_instruction_blocks(
        &mut self, 
        instruction_blocks: Vec<InstructionBlock>, // 接受一个指令块的向量
        // 这个向量包含了所有的指令块，每个指令块都有 start_pc 和 end_pc
        // 以及对应的操作码和栈信息等
    ) -> eyre::Result<()> {
        for block in instruction_blocks {
            self.cfg_dag.add_node((block.start_pc, block.end_pc));
        } // 将每个指令块的 (start_pc, end_pc) 添加到控制流图中
        Ok(())
    } // 这个函数用于初始化控制流图，将给定的指令块添加到图中。

    pub fn form_basic_connections(&mut self) {
        /*
        There are 4 cases of edges that we can connect from basic static analysis:
        1. Jumpi false
        2. Jumpi true (direct jump)
        3. Jump (direct jump)
        4. Block ender is a basic instruction (connect to next pc)
            - this happens when a block is broken up by a jumpdest
        */

        // get last pc in bytecode, this is done by iterating over the instruction blocks and finding the largest end_pc
        let last_pc_total = self
            .map_to_instructionblock
            .iter()
            .map(|((_entry_pc, _exit_pc), instruction_block)| instruction_block.end_pc)
            .max()
            .unwrap(); // 获取字节码的最后一个 pc，这个值是所有指令块的最大 end_pc

        // We need to iterate over each of the nodes in the graph, and check the end_pc of the (start_pc, end_pc) node
        for ((_entry_pc, _exit_pc), instruction_block) in self.map_to_instructionblock.iter() {
            let end_pc = instruction_block.end_pc;
            let start_pc = instruction_block.start_pc;
            let last_op = instruction_block.ops.last().unwrap();
            let _last_op_pc = last_op.0;
            let last_op_code = last_op.1;

            let direct_push = &instruction_block.stack_info.push_used_for_jump;
            let direct_push_val = direct_push.as_ref().copied(); 

            // Case 1: Jumpi false
            if last_op_code == 0x57 {
                // Jumpi false
                let next_pc = end_pc + 1;
                if next_pc >= last_pc_total {
                    // continue;
                } else {
                    let next_node = self.get_node_from_pc(next_pc);
                    self.cfg_dag
                        .add_edge((start_pc, end_pc), next_node, Edges::ConditionFalse);
                }
            }
            if instruction_block.indirect_jump.is_none() && direct_push_val.is_some() {
                // we know this is a direct jump
                // Case 2: Direct Jumpi true
                if last_op_code == 0x57 {
                    // Jumpi true
                    let next_pc = format!("{}", direct_push_val.unwrap())
                        .parse::<u16>()
                        .unwrap(); // this is so stupid but its only done once
                    let next_node = self.get_node_from_pc(next_pc);
                    self.cfg_dag
                        .add_edge((start_pc, end_pc), next_node, Edges::ConditionTrue);
                } 

                // Case 3: Direct Jump
                if last_op_code == 0x56 {
                    // Jump
                    let next_pc = format!("{}", direct_push_val.unwrap())
                        .parse::<u16>()
                        .unwrap(); // this is so stupid but its only done once
                    let next_node = self.get_node_from_pc(next_pc);
                    self.cfg_dag
                        .add_edge((start_pc, end_pc), next_node, Edges::Jump);
                }
            }

            if !BLOCK_ENDERS_U8.contains(&last_op_code)
                && super::opcode(last_op_code).name != "unknown"
            {
                // Block ender is a basic instruction, but not exiting
                let next_pc = end_pc + 1;

                if next_pc >= last_pc_total {
                    continue;
                }
                // println!("next_pc: {}, last_pc_total: {}", next_pc, last_pc_total);

                let next_node = self.get_node_from_pc(next_pc);
                self.cfg_dag
                    .add_edge((start_pc, end_pc), next_node, Edges::Jump);
            } 
        }
    } 

    pub fn remove_unreachable_instruction_blocks(&mut self) {
        // We need to iterate over the nodes in self.map_to_instructionblock, and remove any that have no incoming/outgoing edges and do not begin with a jumpdest
        let mut to_remove: Vec<(u16, u16)> = Vec::new();
        for ((_entry_pc, _exit_pc), instruction_block) in self.map_to_instructionblock.iter() {
            let start_pc = instruction_block.start_pc;
            let end_pc = instruction_block.end_pc;
            let incoming_edges = self
                .cfg_dag
                .edges_directed((start_pc, end_pc), Direction::Incoming);
            if incoming_edges.count() == 0 {
                // This node has no incoming edges, so it is unreachable
                if instruction_block.ops[0].1 != 0x5b && start_pc != 0 {
                    // This node does not begin with a jumpdest, so it is unreachable
                    to_remove.push((start_pc, end_pc));
                }
            }
        }

        // remove the found nodes from the cfg and from the self.map_to_instructionblock
        for node in to_remove {
            self.cfg_dag.remove_node(node);
            self.map_to_instructionblock.remove(&node);
        }
    }

    pub fn get_node_from_pc(&self, pc: u16) -> (u16, u16) {
        for (_key, val) in self.map_to_instructionblock.iter() {
            if val
                .ops
                .iter()
                .map(|(instruction_pc, _op, _push_val)| *instruction_pc == pc)
                .any(|x| x)
            {
                return (val.start_pc, val.end_pc);
            }
        }
        panic!("Could not find node for pc {pc}, hex: {:x}", pc);
    }

    pub fn get_node_from_entry_pc(&self, pc: u16) -> (u16, u16) {
        for (key, val) in self.map_to_instructionblock.iter() {
            if key.0 == pc {
                return (val.start_pc, val.end_pc);
            }
        }
        panic!("Could not find node for entry pc {pc}");
    }

    pub fn get_node_from_exit_pc(&self, pc: u16) -> (u16, u16) {
        for (key, val) in self.map_to_instructionblock.iter() {
            if key.1 == pc {
                return (val.start_pc, val.end_pc);
            }
        }
        panic!("Could not find node for exit pc {pc}");
    }

    pub fn cfg_dot_str_with_blocks(&mut self) -> String {
        let mut dot_str = Vec::new();
        let raw_start_str = r##"digraph G {
    node [shape=box, style="filled, rounded", color="#565f89", fontcolor="#c0caf5", fontname="Helvetica", fillcolor="#24283b"];
    edge [color="#414868", fontcolor="#c0caf5", fontname="Helvetica"];
    bgcolor="#1a1b26";"##;
        dot_str.push(raw_start_str.to_string());

        // 输出所有节点，节点id用"startpc_endpc"
        for ((start_pc, end_pc), block) in self.map_to_instructionblock.iter() {
            let mut attrs = vec![];
            let label = format!("{}", block);
            attrs.push(format!("label = \"{}\"", label.replace("\"", "\\\"")));
            // 高亮
            if let Some(ref pcs) = self.executed_pcs {
                if pcs.contains(start_pc) {
                    attrs.push(format!(
                        "fillcolor = \"{}\" fontcolor = \"#1a1b26\"",
                        TOKYO_NIGHT_COLORS.get("green").unwrap()
                    ));
                }
            }
            // 入口节点特殊形状
            if *start_pc == 0 {
                attrs.push("shape = invhouse".to_string());
            }
            dot_str.push(format!(
                "\"{}_{}\" [{}];",
                start_pc, end_pc,
                attrs.join(" ")
            ));
        }

        // 输出所有边，节点id用"startpc_endpc"
        for (from, to, edge_type) in self.cfg_dag.all_edges() {
            let mut attrs = vec![];
            // 高亮边：如果from和to的start_pc都在executed_pcs里，则高亮
            let mut highlight = false;
            if let Some(ref pcs) = self.executed_pcs {
                if pcs.contains(&from.0) && pcs.contains(&to.0) {
                    highlight = true;
                }
            }
            match edge_type {
                Edges::Jump => {
                    if highlight {
                        attrs.push(format!(
                            "color = \"{}\" penwidth=3",
                            TOKYO_NIGHT_COLORS.get("green").unwrap()
                        ));
                    }
                }
                Edges::ConditionTrue => {
                    if highlight {
                        attrs.push(format!(
                            "label = \"True\" color = \"{}\" penwidth=3",
                            TOKYO_NIGHT_COLORS.get("green").unwrap()
                        ));
                    } else {
                        attrs.push(format!(
                            "label = \"True\" color = \"{}\"",
                            TOKYO_NIGHT_COLORS.get("green").unwrap()
                        ));
                    }
                }
                Edges::ConditionFalse => {
                    if highlight {
                        attrs.push(format!(
                            "label = \"False\" color = \"{}\" penwidth=3",
                            TOKYO_NIGHT_COLORS.get("red").unwrap()
                        ));
                    } else {
                        attrs.push(format!(
                            "label = \"False\" color = \"{}\"",
                            TOKYO_NIGHT_COLORS.get("red").unwrap()
                        ));
                    }
                }
                Edges::SymbolicJump => {
                    if highlight {
                        attrs.push(format!(
                            "label = \"Symbolic\" color = \"{}\" style=\"dotted, bold\" penwidth=3",
                            TOKYO_NIGHT_COLORS.get("yellow").unwrap()
                        ));
                    } else {
                        attrs.push(format!(
                            "label = \"Symbolic\" color = \"{}\" style=\"dotted, bold\"",
                            TOKYO_NIGHT_COLORS.get("yellow").unwrap()
                        ));
                    }
                }
            }
            dot_str.push(format!(
                "\"{}_{}\" -> \"{}_{}\" [{}];",
                from.0, from.1, to.0, to.1,
                attrs.join(" ")
            ));
        }

        dot_str.push("}".to_string());
        dot_str.join("\n")
    }

    pub fn set_executed_pcs(&mut self, pcs: HashSet<u16>) {
        self.executed_pcs = Some(pcs);
    }

    /// 只导出高亮节点和高亮边的 dot 字符串
    pub fn cfg_dot_str_highlighted_only(&self) -> String {
        let mut dot_str = Vec::new();
        let raw_start_str = r##"digraph G {
    node [shape=box, style="filled, rounded", color="#565f89", fontcolor="#1a1b26", fontname="Helvetica"];
    edge [color="#9ece6a", fontcolor="#1a1b26", fontname="Helvetica", penwidth=3];
    bgcolor="#1a1b26";"##;
        dot_str.push(raw_start_str.to_string());

        // 只输出高亮节点
        if let Some(ref pcs) = self.executed_pcs {
            for ((start_pc, end_pc), block) in self.map_to_instructionblock.iter() {
                if pcs.contains(start_pc) {
                    let label = format!("{}", block);
                    // 颜色优先级：SSTORE > ADD/SUB > 其它
                    let mut has_sstore = false;
                    let mut has_add_or_sub = false;
                    for (_pc, op, _push) in &block.ops {
                        let opname = super::opcode(*op).name.to_ascii_lowercase();
                        if opname == "sstore" {
                            has_sstore = true;
                            break;
                        }
                        if opname == "add" || opname == "sub" {
                            has_add_or_sub = true;
                        }
                    }
                    let fillcolor = if has_sstore {
                        "#f7768e" // 红色
                    } else if has_add_or_sub {
                        "#ff9e64" // 橙色
                    } else {
                        "#9ece6a" // 绿色
                    };
                    let mut attrs = vec![
                        format!("label = \"{}\"", label.replace("\"", "\\\"")),
                        format!("fillcolor = \"{}\" fontcolor = \"#1a1b26\"", fillcolor)
                    ];
                    if *start_pc == 0 {
                        attrs.push("shape = invhouse".to_string());
                    }
                    dot_str.push(format!(
                        "\"{}_{}\" [{}];",
                        start_pc, end_pc,
                        attrs.join(" ")
                    ));
                }
            }

            // 只输出高亮边（from、to都高亮）
            for (from, to, _edge_type) in self.cfg_dag.all_edges() {
                if pcs.contains(&from.0) && pcs.contains(&to.0) {
                    dot_str.push(format!(
                        "\"{}_{}\" -> \"{}_{}\";",
                        from.0, from.1, to.0, to.1
                    ));
                }
            }
        }

        dot_str.push("}".to_string());
        dot_str.join("\n")
    }

    // 在 dot 导出时，如果节点/边被执行过，则加高亮色
    // 伪代码示例：
    // if let Some(ref pcs) = self.executed_pcs {
    //     if pcs.contains(&node_pc) {
    //         // 给节点加绿色
    //     }
    // }
}
