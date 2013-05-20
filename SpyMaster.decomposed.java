package csse2002.security;

import csse2002.math.BigFraction;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.TreeSet;

/**
 * Provides methods to read informant files (informant lists) and
 * to equalise the knowledge distribution (informant lists) of two spies.
 */
public class SpyMaster {

    /**
     * Returns a list of of informants containing each
     * ConditionalTwoCoinChannel from the file, in the order in which they
     * appear in the input file. Throws IOException if there is an input
     * error with the input file or FileFormatException of there is an error
     * with the input format.
     *
     * @param fileName The file containing ConditionalTwoCoinChannel records
     * @return A list of informants
     * @throws FileFormatException
     * @throws IOException
     * @require fileName != null
     * @ensure This method reads a text file from fileName with zero or more
     * lines, each of which contains data for a
     * ConditionalTwoCoinChannel. Each line of the file should contain
     * three probabilities separated by one or more whitespaces. The
     * first probability represents the condition of the
     * ConditionalTwoCoinChannel, the second the heads-bias of the first
     * coin of the channel (thrown if the secret is true), and the third
     * the heads-bias of the second coin of the channel (thrown if the
     * secret is false). Each probability is denoted either by a single
     * integer, or by an expression of the form X/Y, where X is an
     * integer and Y is an integer.
     */
    public static List<ConditionalTwoCoinChannel> readInformants
    (String fileName)
            throws FileFormatException, IOException {
        File inputFile = new File(fileName);
        FileReader fileReader = new FileReader(inputFile);

        ArrayList<ConditionalTwoCoinChannel> channels =
                new ArrayList<ConditionalTwoCoinChannel>();

        try {
            BufferedReader bufferedReader = new BufferedReader(fileReader);
            String line = bufferedReader.readLine();

            while (line != null) {
                // loop invariant: line != null
                // loop invariant: bufferedReader != null
                // loop invariant: channels != null

                Integer numerator, denominator;
                BigFraction[] probabilities = new BigFraction[3];

                // Split the current line into its respective fraction entries
                String[] fractions = line.split(" ");

                if (fractions.length != 3)
                    throw new FileFormatException("Encountered invalid " +
                            "ConditionalTwoCoinChannel record");

                // Enumerate the textual representation of each fraction,
                // ensuring valid probabilities and ultimately populating
                // the corresponding BigFraction array element, i
                for (int i = 0; i < fractions.length; i++) {
                    // loop invariant: fractions != null
                    // loop invariant: fractions.length == 3
                    // loop invariant: i < fractions.length
                    // loop invariant: probabilities != null
                    // loop invariant: probabilities.length == 3
                    // loop invariant: i < probabilities.length

                    String fraction = fractions[i];
                    String[] fractionParts = fraction.split("/");

                    if (fractionParts.length == 2) {
                        // The fraction has an explicit denominator
                        numerator = Integer.parseInt(fractionParts[0]);
                        denominator = Integer.parseInt(fractionParts[1]);
                    } else {
                        // The fraction has an implicit denominator of 1
                        numerator = Integer.parseInt(fractionParts[0]);
                        denominator = 1;
                    }

                    BigFraction probability = new BigFraction(
                            numerator, denominator);

                    // Ensure the BigFraction is a valid probability
                    if (!probability.isAProbability())
                        throw new FileFormatException("Encountered an invalid" +
                                " probability");

                    probabilities[i] = probability;
                }

                // Create a new ConditionalTwoCoinChannel from the respective
                // fractional components and add it to the channels list
                channels.add(
                        new ConditionalTwoCoinChannel(
                                probabilities[0],
                                new TwoCoinChannel(
                                        probabilities[1],
                                        probabilities[2])
                        ));

                // Read the next record
                line = bufferedReader.readLine();
            }

        } catch (NumberFormatException e) {
            throw new FileFormatException("Encountered an invalid " +
                    "BigFraction");
        } finally {
            if (fileReader != null)
                fileReader.close();
        }

        return channels;
    }

    private static BigFraction findSmallestInequality (
            BigFraction aPriori,
            List<ConditionalTwoCoinChannel> informantA,
            List<ConditionalTwoCoinChannel> informantB,
            @Out List<ConditionalTwoCoinChannel> smallerInformant,
            @Out List<ConditionalTwoCoinChannel> largerInformant,
            @Out KnowledgeDistribution smallerKD,
            @Out KnowledgeDistribution largerKD
    ){
        BigFraction ks = null; // Smallest Knowledge state

        // The knowledge distribution of spy A
        KnowledgeDistribution kdA = new KnowledgeDistribution(
                aPriori, informantA);
        // The knowledge distribution of spy B
        KnowledgeDistribution kdB = new KnowledgeDistribution(
                aPriori, informantB);

        // The combined and ordered states of kdA and kdB
        TreeSet<BigFraction> orderedStates = new TreeSet<BigFraction>();

        // Add the knowledge-states in kdA to the ordered states list
        for (BigFraction ksA : kdA) {
            orderedStates.add(ksA);
        }

        // Add the knowledge-states in kdB to the ordered states list
        for (BigFraction ksB : kdB) {
            orderedStates.add(ksB);
        }

        // Find the smallest knowledge-state for which kdA(ks) != kdB(ks) and
        // assign ks, x, y, kdX, kdY respectively
        // If kdA is equal to kdB, set ks to null
        FindSmallestInequality:
        for (BigFraction orderedState : orderedStates) {
            // loop invariant: kdA != null
            // loop invariant: kdB != null
            // loop invariant kdA.weight() == 1
            // loop invariant kdB.weight() == 1
            // loop invariant: informants != null
            // loop invariant: informants.size() == 2
            // loop invariant: kdA.weight(orderedState).compareTo(kdB.weight
            //                 (orderedState)) == 0

            ks = orderedState;

            // Determine the higher and lower weighted knowledge distributions
            // @orderedState and assign variables respectively
            switch (kdA.weight(orderedState).compareTo(kdB.weight
                    (orderedState))) {
                case -1:
                    largerInformant = informantB;
                    smallerInformant = informantA;
                    largerKD = kdB;
                    smallerKD = kdA;
                    break FindSmallestInequality;
                case 1:
                    largerInformant = informantA;
                    smallerInformant = informantB;
                    largerKD = kdA;
                    smallerKD = kdB;
                    break FindSmallestInequality;
                default:
                    // No inequality has been found yet
                    ks = null;
            }
        }

        return ks;
    }

    private static void findSupportingElements(
            BigFraction ks,
            KnowledgeDistribution smallerKD,
            KnowledgeDistribution largerKD,
            @Out BigFraction ks0,
            @Out BigFraction ks1
    ){
        // The weight discrepancy between kdX(ks) and kdY(ks)
        BigFraction w = largerKD.weight(ks).subtract(smallerKD.weight(ks));

        Iterator<BigFraction> itY = smallerKD.iterator();

        // Enumerate Y values until the least element in the support of kdY
        // greater than ks is found
        while (itY.hasNext()) {
            // loop invariant: itY != null
            // loop invariant: itY.hashNext()
            // loop invariant: ks != null
            // loop invariant itY.next().compareTo(ks) != 1
            // Note: ks0 will never be null per
            // KnowledgeDistribution(aPriori, {})

            ks0 = itY.next();

            // ks1 be either 1 if ks0 is the largest element in the support
            // of kdY, or the next-largest knowledge-state after ks0 in the
            // support of kdY, otherwise.
            if (ks0.compareTo(ks) == 1) {
                // ks1 is equal to ks0 if there are no more supporting
                // elements in itY
                // otherwise ks1 is the next-large element in itY
                ks1 = itY.hasNext() ? itY.next() : BigFraction.ONE;
                break;
            }
        }
    }

    /**
     * Recursively extends each list of informants until their respective
     * knowledge distributions are equal
     *
     * @param aPriori    The knowledge-state from which the knowledge
     *                   distributions will be created.
     * @param informants The list of each spy's informant list
     * @require Parameter aPriori is a probability. Parameter informants is a
     * list containing two (possibly empty) lists of non-null
     * ConditionalTwoCoinChannels. (As such, neither parameter is null
     * or contains null-values.)
     * @ensure This method extends each list \old(informants).get(0) and
     * \old(informants).get(1) with zero or more informants such that
     * kd0 "is equivalent to" kd1
     * for kd0 = new KnowledgeDistribution(aPriori, informants.get(0))
     * and kd1 = new KnowledgeDistribution(aPriori, informants.get(1))
     * and for any alternative extension of these lists informants' such that
     * kd0' "is equivalent to" kd1'
     */
    public static void findAdditionalInformants(
            BigFraction aPriori,
            List<List<ConditionalTwoCoinChannel>> informants
    ) {
        // The smallest knowledge-state for which kdA(ks) != kdB(ks)
        BigFraction ks = null;
        // The informant list of the spy with the greater weight
        List<ConditionalTwoCoinChannel> x = null;
        // The informant list of the spy with the lesser weight
        List<ConditionalTwoCoinChannel> y = null;
        // The informant list of the spy with the greater weight
        KnowledgeDistribution kdX = null;
        // The informant list of the spy with the lesser weight
        KnowledgeDistribution kdY = null;
        //  The difference in weight kdX(ks) – kdY(ks).
        BigFraction w = null;
        // The least element in the support of kdY greater than ks.
        BigFraction ks0 = null;
        // Either 1 if ks0 is the largest element in the support of kdY,
        // or the next-largest  knowledge-state after ks0 in the support of kdY,
        BigFraction ks1 = null;
        // w min kdY(ks0)*(ks1-ks0)/(ks1-ks)
        BigFraction r = null;

        ks = findSmallestInequality(
                aPriori,
                informants.get(0),
                informants.get(1),
                @Out y,
                @Out x,
                @Out kdY,
                @Out kdX
        );

        // ks0 and ks1 are equal; no further informants required
        if (ks == null)
            return;

        findSupportingElements(
                ks,
                kdY,
                kdX,
                @Out ks0,
                @Out ks1
        );

        // Note: ks0 will never be null per
        // KnowledgeDistribution(BigFraction, List<ConditionalTwoCoinChannel>)

        r = kdY.weight(ks0).multiply(
                ks1.subtract(ks0)
        ).divide(ks1.subtract(ks));
        r = r.compareTo(w) == -1 ? r : w;

        // The condition of the informant to add
        BigFraction condition = ks0;
        // The the aPosteriori(true) value of the informant to add
        BigFraction aPosterioriTrue = ks;
        // The the outcomeProbability(true) value of the informant to add
        BigFraction outcomeProbabilityTrue = r.divide(kdY.weight(ks0));

        // The value of coin1 in the informant to add
        // coin1 = (coin1 * condition) / outcomeProbabilityTrue
        BigFraction coin1 = aPosterioriTrue.multiply(outcomeProbabilityTrue)
                .divide(condition);

        // The value of coin2 in the informant to add
        // outcomeProbabilityTrue = (condition * coin1) + (coin2 *
        // condition.complement())
        BigFraction coin2 = outcomeProbabilityTrue.subtract(
                condition.multiply(coin1)
        ).divide(condition.complement());

        // The informant to add
        ConditionalTwoCoinChannel ch = new ConditionalTwoCoinChannel(
                condition,
                new TwoCoinChannel(coin1, coin2)
        );

        // Add the informant to the spy with the lesser weight
        y.add(ch);

        // Continue to add informants until the knowledge distribution of
        // both spies (kdA, kdB) are equal
        findAdditionalInformants(aPriori, informants);
    }
}
