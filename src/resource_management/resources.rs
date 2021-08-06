
#[derive(Clone, Copy, Debug, Default)]
pub struct Resources {
    pub cpu_cores: usize,
    pub fpga_units: usize,
    pub fpga_memory: usize,
    pub gpu_units: usize,
    pub gpu_memory: usize
}

pub(crate) fn try_get_res(all_res: &mut Resources, requested: Resources) -> bool {
    if all_res.cpu_cores < requested.cpu_cores {
        return false
    }

    all_res.cpu_cores -= requested.cpu_cores;
    all_res.fpga_units -= requested.fpga_units;
    all_res.fpga_memory -= requested.fpga_memory;
    all_res.gpu_units -= requested.gpu_units;
    all_res.gpu_memory -= requested.gpu_memory;

    true
}

pub(crate) fn return_res(all_res: &mut Resources, returned: Resources) {
    all_res.cpu_cores += returned.cpu_cores;
    all_res.fpga_units += returned.fpga_units;
    all_res.fpga_memory += returned.fpga_memory;
    all_res.gpu_units += returned.gpu_units;
    all_res.gpu_memory += returned.gpu_memory;
}