import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
import paillierp.Paillier;
import paillierp.key.PaillierKey;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.*;
import java.math.BigInteger;
import java.util.Random;

public class CaptureCodes_Reader {

    static public void main(String[] args) throws IOException, ClassNotFoundException, ParserConfigurationException, SAXException, InterruptedException {
        while (true) {
            procedure();
            Thread.sleep(30000);
            for (int i = 0; i < 25; ++i)
                System.out.println();
        }
    }

    private static void procedure() throws IOException, SAXException, ParserConfigurationException, ClassNotFoundException {
        BigInteger publicKeyN = recoverPublicKey("publicValueForEncryption/publicKeyN.key");

        PaillierKey publicKey = new PaillierKey(publicKeyN, new Random());
        Paillier p = new Paillier(publicKey);

        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));

        System.out.println(" *********************************************************** ");
        System.out.println(" * Bienvenido al Verificador de la Encriptación de su Voto * ");
        System.out.println(" *********************************************************** ");
        System.out.println();

        System.out.println("Escanee el PRIMER Código QR (Encriptación de su voto)");
        String ballotWithSignature = br.readLine();

        int sep = Integer.parseInt(ballotWithSignature.substring(0, 3));
        BigInteger ballot = new BigInteger(ballotWithSignature.substring(3, sep+3));

        System.out.println();
        System.out.println("Escanee el SEGUNDO Código QR (Aleatoriedad utilizada)");
        String randomnessString = br.readLine();
        System.out.println();

        BigInteger randomness = new BigInteger(randomnessString);

        String[] candidates = setCandidates("candidates/");
        byte[] possibleBallot = new byte[candidates.length + 1];
        possibleBallot[0] = 1;
        boolean success = false;

        for (int i = 0; i < possibleBallot.length - 1; i++){
            possibleBallot[i+1] = 1;
            BigInteger enc = p.encrypt(new BigInteger(possibleBallot), randomness);
            if (enc.equals(ballot)) {
                System.out.println("El voto encriptado es: " + candidates[i]);
                success = true;
                break;
            }
            else
                possibleBallot[i+1] = 0;
        }

        if (!success)
            System.out.println("No ha sido encriptado un voto válido, repetir el proceso de generación de la papeleta.");
        else {
            System.out.println();
            System.out.println("Si está de acuerdo con la encriptación, proceda a doblar la primera parte del voto y dirigirse a la mesa de votación.");
            System.out.println("Si no, puede repetir el proceso de generación de papeleta.");
            System.out.println("\nGracias por operar con el Verificador de la Encriptación de votos.");
        }
    }

    private static BigInteger recoverPublicKey(String fileName) throws IOException, ClassNotFoundException {
        ObjectInputStream oin = new ObjectInputStream(new BufferedInputStream(new FileInputStream(fileName)));
        BigInteger publicKeyN = (BigInteger) oin.readObject();
        return publicKeyN;
    }

    private static String[] setCandidates(String folderName) throws ParserConfigurationException, IOException, SAXException {
        String[] candidates;
        File file = new File(folderName + "candidates.xml");
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = dbf.newDocumentBuilder();
        Document doc = db.parse(file);
        doc.getDocumentElement().normalize();

        NodeList nodeLst = doc.getElementsByTagName("integer");
        int numberOfCandidates = Integer.parseInt(nodeLst.item(0).getTextContent());
        candidates = new String[numberOfCandidates + 1];
        nodeLst = doc.getElementsByTagName("string");

        for (int i = 0 ; i < nodeLst.getLength() ; i++) {
            Node node = nodeLst.item(i);
            candidates[i] = node.getTextContent();
        }

        return candidates;
    }



}
