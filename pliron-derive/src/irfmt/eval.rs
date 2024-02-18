use proc_macro2::Span;
use syn;

use super::{Directive, Elem, FieldIdent, FmtValue, Format, Optional};

pub struct AttribTypeFmtEvaler<'a> {
    span: Span,
    fields: &'a [FieldIdent],
}

impl<'a> AttribTypeFmtEvaler<'a> {
    pub fn new(span: Span, fields: &'a [FieldIdent]) -> Self {
        Self { span, fields }
    }

    fn span(&self) -> Span {
        self.span
    }

    pub fn eval(&self, f: Format) -> syn::Result<Format> {
        Ok(self.eval_format(f, true)?.into())
    }

    fn eval_format(&self, f: Format, toplevel: bool) -> syn::Result<Format> {
        let elems = self.eval_elems(f.elems, toplevel)?;
        Ok(elems.into())
    }

    fn eval_elems(&self, elem: Vec<Elem>, toplevel: bool) -> syn::Result<FmtValue> {
        let results = elem.into_iter().map(|e| self.eval_elem(e, toplevel));
        let mut elems = vec![];
        for r in results {
            r?.flatten_into(&mut elems);
        }
        Ok(FmtValue(elems))
    }

    fn eval_elem(&self, elem: Elem, toplevel: bool) -> syn::Result<FmtValue> {
        match elem {
            Elem::Lit(_) | Elem::Var(_) | Elem::UnnamedVar(_) => Ok(elem.into()),
            Elem::Directive(d) => self.eval_directive(d, toplevel),
            Elem::Optional(opt) => self.eval_optional(opt, toplevel),
        }
    }

    fn eval_directive(&self, d: Directive, toplevel: bool) -> syn::Result<FmtValue> {
        match d.name.as_str() {
            "params" => {
                require_no_args(self.span, "params", &d.args)?;
                if toplevel {
                    Ok(FmtValue::from(d))
                } else {
                    Ok(FmtValue::from(
                        self.fields.iter().map(|f| f.into()).collect::<Vec<_>>(),
                    ))
                }
            }
            "struct" => {
                require_toplevel(self.span, &d.name, toplevel)?;
                require_args(self.span, "struct", &d.args)?;
                let args = self.eval_args(d.args)?;
                Ok(FmtValue::from(Directive { args, ..d }))
            }
            _ => {
                require_toplevel(self.span, &d.name, toplevel)?;
                let args = self.eval_args(d.args)?;
                Ok(FmtValue::from(Directive { args, ..d }))
            }
        }
    }

    fn eval_args(&self, args: Vec<Elem>) -> syn::Result<Vec<Elem>> {
        let values = self.eval_elems(args, false)?;
        Ok(values.into())
    }

    fn eval_optional(&self, opt: Optional, toplevel: bool) -> syn::Result<FmtValue> {
        require_toplevel(self.span(), "optional", toplevel).unwrap();

        let mut check_tmp = self.eval_elem(*opt.check, false)?.flatten();
        let Some(check) = check_tmp.pop() else {
            return Err(syn::Error::new(
                self.span(),
                "`check` argument of `optional` has no value",
            ));
        };
        if !check_tmp.is_empty() {
            return Err(syn::Error::new(
                self.span(),
                "`check` argument of `optional` directive must be a single value",
            ));
        }

        let then_format = self.eval_format(opt.then_format, toplevel)?;
        let else_format = opt
            .else_format
            .map(|f| self.eval_format(f, toplevel))
            .transpose()?;

        Ok(FmtValue::from(Optional {
            check: Box::new(check),
            then_format,
            else_format,
        }))
    }
}

fn require_toplevel(span: Span, directive: &str, toplevel: bool) -> syn::Result<()> {
    if !toplevel {
        return Err(syn::Error::new(
            span,
            format!("`{}` directive is only allowed at the top-level", directive),
        ));
    }
    Ok(())
}

fn require_no_args(span: Span, directive: &str, args: &[Elem]) -> syn::Result<()> {
    if !args.is_empty() {
        return Err(syn::Error::new(
            span,
            format!("`{}` directive does not take any arguments", directive),
        ));
    }
    Ok(())
}

fn require_args(span: Span, directive: &str, args: &[Elem]) -> syn::Result<()> {
    if args.is_empty() {
        return Err(syn::Error::new(
            span,
            format!("`{}` directive requires arguments", directive),
        ));
    }
    Ok(())
}
