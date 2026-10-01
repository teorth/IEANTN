from test_ieantn import FixtureRepo, ieantn


class TestToolchainStaleness(FixtureRepo):
    def test_same_mathlib_does_not_hide_changed_or_missing_toolchain(self):
        current = ieantn.current_environment()
        for toolchain in ('leanprover/lean4:v4.34.0-rc1', None):
            with self.subTest(toolchain=toolchain):
                environment = {'mathlib_rev': current['mathlib_rev']}
                if toolchain is not None:
                    environment['lean_toolchain'] = toolchain
                receipt = {'statement': {'A.v1.main': 'd'}, 'environment': environment}
                light, detail = ieantn.assess('A.v1.main', receipt, {'A.v1.main': 'd'})
                self.assertEqual(light, 'yellow')
                self.assertIn('toolchain', detail)
