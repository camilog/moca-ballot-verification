import java.math.BigInteger;

public class PlainVote {

    int numberOfCandidates;
    int candidateSelected; // 1 to numberOfCandidates+1
    byte[] voteByteArray;

    public PlainVote(int numberOfCandidates, int candidateSelected){
        this.numberOfCandidates = numberOfCandidates;
        this.candidateSelected = candidateSelected;
        this.voteByteArray = new byte[(numberOfCandidates+1)*4];
        this.voteByteArray[(candidateSelected*4)-1] = 1;
    }

    public BigInteger toBigInteger() {
        return new BigInteger(this.voteByteArray);
    }

}
