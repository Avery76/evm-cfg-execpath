use crate::cfg_gen::{dasm::InstructionBlock, *};
use clap::{ArgAction, Parser, ValueHint};
use evm_cfg::OutputHandler;
use fnv::FnvBuildHasher;
use revm::primitives::{Bytecode, Bytes};
use revm::interpreter::analysis::to_analysed;
use std::{
    collections::{BTreeMap, HashSet},
    io::Write,
    process::Command,
};

pub mod cfg_gen;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Either a path to a file containing the bytecode or the bytecode itself
    #[clap(value_hint = ValueHint::FilePath, value_name = "PATH or BYTECODE")]
    pub path_or_bytecode: String,

    /// Filename and format for storing the analyzed cfg. Supports all standard
    /// graphviz formats (*.dot, *.png, *.jpg, ...). Default is stdout in dot format
    #[clap(long, short)]
    pub output: Option<String>,

    /// Whether to open saved dot visualization of the analyzed cfg with associated application
    #[clap(long, default_value = "false")]
    pub open: bool,

    /// Verbosity of the cfg creator
    #[clap(long, short, action = ArgAction::Count)]
    pub verbosity: u8,

    /// Optional: Path to a transaction trace JSON file
    #[clap(long)]
    pub trace: Option<String>,

    /// The contract address (hex, e.g. 0x1234...) to highlight in trace
    #[clap(long)]
    pub contract: String,
}

fn main() {
    let args = Args::parse();
    let path_string = args.path_or_bytecode;
    let bytecode_string = std::fs::read_to_string(&path_string).unwrap_or(path_string);
    let bytecode_string = bytecode_string.replace(['\n', ' ', '\r'], "");

    let verbosity = args.verbosity;
    let output_handler: OutputHandler = match verbosity {
        0 => OutputHandler::default(),
        1 => OutputHandler {
            show_timings: true,
            ..Default::default()
        },
        2 => OutputHandler {
            show_timings: true,
            show_basic_connections: true,
            ..Default::default()
        },
        3 => OutputHandler {
            show_timings: true,
            show_basic_connections: true,
            show_bare_nodes: true,
            ..Default::default()
        },
        4 => OutputHandler {
            show_timings: true,
            show_basic_connections: true,
            show_bare_nodes: true,
            show_jump_dests: true,
        },
        11 => OutputHandler {
            show_timings: true,
            show_basic_connections: true,
            show_bare_nodes: true,
            show_jump_dests: true,
        },
        _ => OutputHandler {
            show_timings: true,
            show_basic_connections: true,
            show_bare_nodes: true,
            show_jump_dests: true,
        },
    };

    // DISASSEMBLY
    let disassembly_time = std::time::Instant::now();
    // get jumptable from revm
    let contract_data: Bytes = hex::decode(&bytecode_string).unwrap().into();
    let bytecode_analysed = to_analysed(Bytecode::new_raw(contract_data));
    let revm_jumptable = bytecode_analysed.legacy_jump_table().expect("revm bytecode analysis failed");

    // convert jumptable to HashSet of valid jumpdests using as_slice
    let mut set_all_valid_jumpdests: HashSet<u16, FnvBuildHasher> = HashSet::default();
    let slice = revm_jumptable.as_slice();
    for (byte_index, &byte) in slice.iter().enumerate() {
        for bit_index in 0..8 {
            if byte & (1 << bit_index) != 0 {
                let pc = (byte_index * 8 + bit_index) as u16;
                set_all_valid_jumpdests.insert(pc);
            }
        }
    }

    if output_handler.show_jump_dests {
        println!("all valid jumpdests: {:?}", &set_all_valid_jumpdests);
    }

    // convert bytecode to instruction blocks
    let mut instruction_blocks = dasm::disassemble(bytecode_analysed.original_byte_slice().into());

    for block in &mut instruction_blocks {
        block.analyze_stack_info();
    }

    let mut map_to_instructionblocks: BTreeMap<(u16, u16), InstructionBlock> = instruction_blocks
        .iter()
        .map(|block| ((block.start_pc, block.end_pc), block.clone()))
        .collect();

    // 1. 先收集 executed_blocks
    let contract_address = args.contract.to_lowercase();

    let mut executed_blocks = std::collections::HashSet::new();
    if let Some(trace_path) = &args.trace {
        let trace_steps = cfg_gen::trace::parse_trace_file(trace_path).unwrap();
        for step in &trace_steps {
            if let (Some(pc), Some(addr_hex)) = (step.pc, step.address_hex()) {
                if addr_hex.to_lowercase() == contract_address {
                    for ((start_pc, end_pc), _block) in &map_to_instructionblocks {
                        if *start_pc <= pc && pc <= *end_pc {
                            executed_blocks.insert(*start_pc);
                            break;
                        }
                    }
                }
            }
        }
    }

    println!("executed_blocks: {:?}", executed_blocks);

    // 2. 创建 CFGRunner
    let mut cfg_runner = cfg_gen::cfg_graph::CFGRunner::new(
        bytecode_analysed.original_byte_slice().into(),
        &mut map_to_instructionblocks,
    );

    // 3. 设置高亮
    if !executed_blocks.is_empty() {
        cfg_runner.set_executed_pcs(executed_blocks);
    }

    if output_handler.show_bare_nodes {
        // write out the cfg with bare nodes only
        let mut file = std::fs::File::create("cfg_nodes_only.dot").expect("bad fs open");
        file.write_all(cfg_runner.cfg_dot_str_with_blocks().as_bytes())
            .expect("bad file write");
    }

    // form basic edges based on direct pushes leading into jumps, false edges of jumpis, and pc+1 when no jump is used
    cfg_runner.form_basic_connections();
    // trim instruction blocks from graph that have no incoming edges and do not lead the block with a jumpdest
    cfg_runner.remove_unreachable_instruction_blocks();

    if output_handler.show_timings {
        println!("disassembly took: {:?}", disassembly_time.elapsed());
    }

    if output_handler.show_basic_connections {
        // write out the cfg with basic connections only
        let mut file = std::fs::File::create("cfg_basic_connections.dot").expect("bad fs open");
        file.write_all(cfg_runner.cfg_dot_str_with_blocks().as_bytes())
            .expect("bad file write");
    }

    let stack_solve_time = std::time::Instant::now();
    // find new edges based on indirect jumps
    let label_symbolic_jumps = false;
    stack_solve::symbolic_cycle(
        &mut cfg_runner,
        &set_all_valid_jumpdests,
        label_symbolic_jumps,
    );

    if output_handler.show_timings {
        println!("stack_solve took: {:?}", stack_solve_time.elapsed());
    }

    // write out the cfg with found indirect edges
    if let Some(filename) = &args.output {
        let mut file = std::fs::File::create(filename).expect("bad fs open");
        // 只用 cfg_dot_str_with_blocks
        file.write_all(cfg_runner.cfg_dot_str_with_blocks().as_bytes())
            .expect("bad file write");
        println!("Dot file saved to {}", &filename);

        let ext = filename.split('.').last().unwrap();
        if ext != "dot" {
            let output = Command::new("dot")
                .arg(format!("-T{}", ext))
                .arg("-o")
                .arg(filename) // output file
                .arg(filename) // file to read
                .output()
                .expect("failed to execute process");

            if output.stderr.is_empty() {
                println!("File saved to {}", &filename);
            }
        }
    } else {
        println!("{}", cfg_runner.cfg_dot_str_with_blocks());
    };

    // 生成只包含高亮路径的 dot 文件
    let mut file = std::fs::File::create("highlighted_only.dot").expect("bad fs open");
    file.write_all(cfg_runner.cfg_dot_str_highlighted_only().as_bytes())
        .expect("bad file write");
    println!("Dot file saved to highlighted_only.dot");

    if args.open {
        if let Some(filename) = &args.output {
            open::that(filename).expect("failed to open the doc");
        } else {
            eprintln!(
                "Cannot open file that was not saved. Consider specifying output with --output"
            );
        }
    }
}
