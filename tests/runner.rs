use pika3::*;

struct Test {
    result: ElabResult,
    errors: Vec<ElabError>,
}
impl Test {
    fn write_errs(&self) {
        for e in &self.errors {
            e.write_err(&self.result.db);
        }
    }

    fn succeeds(self) -> Test {
        if !self.errors.is_empty() {
            self.write_errs();
            panic!("Test failed with {} errors", self.errors.len())
        }
        self
    }

    fn num_errors(self, n: usize) -> Test {
        assert_eq!(self.errors.len(), n);
        self
    }
}
fn test(files: &[&str]) -> Test {
    let files: Vec<_> = files
        .iter()
        .map(|x| format!("tests/{}", x).into())
        .collect();
    let mut result = elab_files(&files).unwrap();
    let errors = result.all_errors();
    Test { result, errors }
}

#[test]
fn demo() {
    test(&["Demo.pk"]).succeeds();
}

#[test]
fn demo_errors() {
    // TODO: this is fine for now but i think some of these errors are duplicates that we should try to get rid of at some point
    test(&["DemoErr.pk"]).num_errors(55);
}

#[test]
fn multifile() {
    test(&["Multifile/One.pk", "Multifile/Two.pk"]).succeeds();
}

#[test]
fn sum_type() {
    test(&["SumType.pk"]).succeeds();
}

#[test]
fn regions() {
    test(&["Regions.pk"]).num_errors(2);
}

#[test]
fn local_def() {
    test(&["LocalDef.pk"]).succeeds();
}
