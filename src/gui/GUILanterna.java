package gui;

import com.googlecode.lanterna.TerminalPosition;
import com.googlecode.lanterna.graphics.Theme;
import com.googlecode.lanterna.graphics.ThemeDefinition;
import com.googlecode.lanterna.gui2.*;
import com.googlecode.lanterna.gui2.dialogs.MessageDialog;
import com.googlecode.lanterna.gui2.dialogs.MessageDialogButton;
import com.googlecode.lanterna.gui2.dialogs.TextInputDialog;
import com.googlecode.lanterna.screen.Screen;
import com.googlecode.lanterna.screen.TerminalScreen;
import com.googlecode.lanterna.terminal.DefaultTerminalFactory;
import com.googlecode.lanterna.terminal.Terminal;

import crypto.BallotVerification;

import org.xml.sax.SAXException;
import javax.xml.parsers.ParserConfigurationException;
import java.io.IOException;
import java.util.Arrays;

public class GUILanterna {

    private static void updatePublicInformationLabel(Panel publicInformationPanel) {

        Label publicKeyLabel = (Label) publicInformationPanel.getChildren().toArray()[0];
        Label candidatesFileLabel = (Label) publicInformationPanel.getChildren().toArray()[1];

        if (BallotVerification.getPaillierPublic() != null)
            publicKeyLabel.setText("Public Key: YES");

        if (BallotVerification.getCandidates() != null)
            candidatesFileLabel.setText("Candidates File: YES");

    }

    public static void main(String[] args) throws IOException {

        // Setup terminal and screen layers
        Terminal terminal = new DefaultTerminalFactory().createTerminal();
        Screen screen = new TerminalScreen(terminal);
        screen.startScreen();

        // Setup MultiWindowTextGUI for dialogs
        WindowBasedTextGUI gui = new MultiWindowTextGUI(screen);

        Panel panel = new Panel();
        panel.addComponent(new Label("Public Key: NO"));
        panel.addComponent(new Label("Candidates File: NO"));

        panel.addComponent(new Button("Configure Public Information", () -> {
            String candidates = TextInputDialog.showDialog(gui, "Codes Reader", "Read Candidates QR-Code", "");
//            String candidates = new TextInputDialogBuilder()
//                    .setTitle("Read Candidates QR-Code")
//                    .setTextBoxSize(new TerminalSize(35,5))
//                    .build()
//                    .showDialog(gui);
            String publicKey = TextInputDialog.showDialog(gui,"Codes Reader", "Read Public Key QR-Code","");
//            String publicKey = new TextInputDialogBuilder()
//                    .setTitle("Read Public Key QR-Code")
//                    .setTextBoxSize(new TerminalSize(35,5))
//                    .build()
//                    .showDialog(gui);

            try {
                BallotVerification.publicConfiguration(candidates, publicKey);
                updatePublicInformationLabel(panel);
            } catch (IOException | ClassNotFoundException | SAXException | ParserConfigurationException e) {
                e.printStackTrace();
            }

        }));

        // Add button to initialize application
        panel.addComponent(new Button("Initialize verification", () -> {
            // TODO: apretar OK automaticamente en las nuevas ventanas, luego de introducir código QR

            // Retrieve first QR-Code (encryptedBallot + signature)
            String encryptedBallotWithSignature = TextInputDialog.showDialog(gui, "Codes Reader", "Read FIRST QR-Code", "");
            // TODO: Check if the user pressed 'Cancel' -> La idea es que no sea posible, debido a apretar automáticamente 'OK'

            // Retrieve second QR-Code (randomness used to encrypt)
            String randomnessString = TextInputDialog.showDialog(gui, "Codes Reader", "Read SECOND QR-Code", "");
            // TODO: Check if the user pressed 'Cancel' -> La idea es que no sea posible, debido a apretar automáticamente 'OK'

            // Apply algorithm to try all possible candidates and stores in encryptedCandidate the one who is actually encrypted
            BallotVerification.ballotConfiguration(encryptedBallotWithSignature, randomnessString);
            String finalCandidate = BallotVerification.verification();

            // Final message which shows the encryptedCandidate, if none, shows an empty String
            MessageDialog.showMessageDialog(gui, "Encrypted objects.Candidate", finalCandidate, MessageDialogButton.OK);
            // TODO: Reiniciar aplicación luego de pasado un cierto tiempo

        }));

        // Add button to finalize application
        panel.addComponent(new Button("Exit application", () -> {
            // Close window properly and finalize application
            try {
                gui.getScreen().clear();
                gui.getScreen().refresh();
                gui.getScreen().setCursorPosition(new TerminalPosition(0, 0));
                gui.getScreen().refresh();
                gui.getScreen().stopScreen();
            } catch (IOException ignored) {

            }
            System.exit(0);
        }));

        // Create window to hold the panel
        BasicWindow window = new BasicWindow();
        window.setComponent(panel);
        updatePublicInformationLabel(panel);
        window.setHints(Arrays.asList(Window.Hint.CENTERED));

        // Start gui
        gui.addWindowAndWait(window);

        // Refresh screen
        screen.refresh();

        // Stopping screen at finalize application
        screen.stopScreen();

    }

}
