import test from 'node:test';
import assert from 'node:assert/strict';
import {buildExecutionTrace} from '../../docs/web/hub/paralliverse/execution-stepper.mjs';

test('packing keeps the real CPU and GPU paths visibly distinct', () => {
  const trace = buildExecutionTrace({mode: 'pack', cpuWords: [8, 3, 8, 0], gpuWords: [8, 3, 8, 0]});
  assert.deepEqual(trace.cpuSteps.map(s => s.title), [
    'Lean packet preparation', 'Lean sequential specification', 'Actual CPU output']);
  assert.deepEqual(trace.gpuSteps.map(s => s.title), [
    'Upload prepared packet', 'Count', 'Scan', 'Stable scatter', 'Actual GPU readback']);
  assert.equal(trace.matches, true);
  assert.match(trace.difference, /Exact payload equality: 4 words/);
  assert.match(trace.gpuSteps[2].detail, /single GPU invocation|One invocation/);
});
test('a GPU refusal is not displayed as a successful GPU result', () => {
  const studio = {
    sourceIR: '.seq a b', optimizedIR: '.map f', steps: Array.from({length: 3}, () => ({kernel: 'add', operand: 1})),
    gpuEligible: false, refusal: 'Three maps are not supported by the GPU selector.',
    input: [3], output: [6], executionPlan: null,
  };
  const trace = buildExecutionTrace({mode: 'studio', cpuWords: studio.output, studio});
  assert.equal(trace.gpuSteps.length, 1);
  assert.equal(trace.gpuSteps[0].status, 'refused');
  assert.equal(trace.matches, null);
  assert.match(trace.difference, /No GPU comparison/);
});
test('actual different payloads are reported with exact mismatch indices', () => {
  const trace = buildExecutionTrace({mode: 'pack', cpuWords: [0, 9, 0], gpuWords: [0, 7, 1]});
  assert.equal(trace.matches, false);
  assert.deepEqual(trace.mismatches, [{index: 1, cpu: 9, gpu: 7}, {index: 2, cpu: 0, gpu: 1}]);
});
test('CPU-only zero-word output is recorded but not misrepresented as GPU success', () => {
  const trace = buildExecutionTrace({mode: 'pack', cpuWords: [], gpuState: 'adapter-unavailable'});
  assert.equal(trace.cpuSteps.at(-1).status, 'observed');
  assert.equal(trace.gpuSteps.at(-1).status, 'planned');
  assert.equal(trace.matches, null);
  assert.match(trace.difference, /GPU unavailable/);
});
test('two actual GPU pass descriptors remain sourced from Lean plan', () => {
  const studio = {
    sourceIR: '.seq m a', optimizedIR: '.map ma', input: [1, 2], output: [4, 7],
    steps: [{kernel: 'multiply', operand: 3}, {kernel: 'add', operand: 1}],
    gpuEligible: true, executionPlan: {
      wordCount: 2, workgroups: 1, buffers: [{}, {}, {}],
      passes: [{kernel: 'multiply', operand: 3, shaderSelector: 4, sourceBuffer: 0, destinationBuffer: 1},
        {kernel: 'add', operand: 1, shaderSelector: 3, sourceBuffer: 1, destinationBuffer: 2}],
    },
  };
  const trace = buildExecutionTrace({mode: 'studio', cpuWords: studio.output,
    studio, gpuWords: [4, 7], gpuMeta: {fullMatches: true}});
  assert.deepEqual(trace.gpuSteps.map(s => s.title), [
    'Lean GPU plan and input buffers', 'GPU pass 1: multiply', 'GPU pass 2: add', 'Actual GPU readback']);
  assert.match(trace.gpuSteps[2].detail, /Source buffer 1 → destination buffer 2/);
  assert.equal(trace.matches, true);
});

test('whole-GPU-buffer mismatch is not painted green despite identical payloads', () => {
  const studio = {
    sourceIR: '.map (.prim (.add 1))', optimizedIR: '.map (.prim (.add 1))',
    input: [1], output: [2], steps: [{kernel: 'add', operand: 1}],
    gpuEligible: true, executionPlan: {wordCount: 1, workgroups: 1,
      buffers: [{}, {}], passes: [{kernel: 'add', operand: 1, shaderSelector: 3,
        sourceBuffer: 0, destinationBuffer: 1}]},
  };
  const trace = buildExecutionTrace({mode: 'studio', studio,
    cpuWords: [2], gpuWords: [2], gpuMeta: {fullMatches: false, canariesMatch: false}});
  assert.equal(trace.matches, false);
  assert.deepEqual(trace.mismatches, []);
  assert.match(trace.difference, /complete buffer frame differs/);
});
