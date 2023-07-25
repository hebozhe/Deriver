"""Welcome to Reflex! This file outlines the steps to create a basic app."""
from Deriver.bzns.primitives import SYM_CONV
import reflex as rx
from rxconfig import config

docs_url: str = "https://reflex.dev/docs/getting-started/introduction"
filename: str = f"{config.app_name}/{config.app_name}.py"


class State(rx.State):
    """The app state."""


class InputState(rx.State):
    """
    The state of the input.
    """

    fmla_list: list[str] = ["A", "A→B", "B"]
    label_text: str = f"Derive: A, A→B ⊢ B"

    def update_fmla_list_and_label(self, text: str) -> None:
        """
        Format the label text to resemble a Gentzen sequent,
        and update the formula list to reflect the inputs.

        Args:
            text (str): The input string to be checked.

        Returns
            None
        """

        # Update the label text.
        for sym_str, conv in SYM_CONV.items():
            text = text.replace(sym_str, conv)
        self.fmla_list = [f.strip() for f in text.split(",") if f.strip()]

        if not self.fmla_list:
            self.label_text = "Derive something."
            return None

        prems: str = ", ".join(self.fmla_list[:-1]) if self.fmla_list[:-1] else ""
        self.label_text = f"Derive: {prems} ⊢ {self.fmla_list[-1]}."

        return None


def index() -> rx.Component:
    """
    This function houses the frontend components for the homepage.
    """
    return rx.vstack(
        *(
            rx.text(InputState.label_text),
            rx.input(
                placeholder="A, A→B, B",
                on_change=InputState.update_fmla_list_and_label,
            ),
            rx.text("Separate each formula with commas."),
        )
    )


# Add state and page to the app.
app = rx.App(state=InputState)
app.add_page(index)
app.compile()
