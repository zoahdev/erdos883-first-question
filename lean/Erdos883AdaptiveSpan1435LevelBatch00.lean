import Erdos883AdaptiveCertificate1435Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1435_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 11003454148089019472781006379187959579398920005218345264865479073149088560458880482181341700286543616689653182557575924118737398849405861770700603675056125147413634339462966678700788664182863783272324644955905851653742390961438534875183388111057745383120680417874673728
def adaptiveNumericSpans1435_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1435_0Chunk0].flatten
def adaptiveSpanEven1435_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 718 0 adaptiveNumericSpans1435_0)
def adaptiveSpanWhole1435_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1435_0)
theorem adaptiveSpanNumericCheck1435_0 : coreNumericSpansCheck 1400 6 480 1155 adaptiveNumericSpans1435_0 adaptiveRows1435 = true := by decide +kernel
theorem adaptiveSpanEvenCache1435_0 : adaptiveSpanEven1435_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1435_0 : adaptiveSpanEven1435_0.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1435_0 : adaptiveSpanEven1435_0.spans = coreEvenSpans 718 0 adaptiveNumericSpans1435_0 := by decide +kernel
theorem adaptiveSpanWholeCache1435_0 : adaptiveSpanWhole1435_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1435_0 : adaptiveSpanWhole1435_0.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1435_0 : adaptiveSpanWhole1435_0.spans = coreWholeSpans 0 adaptiveNumericSpans1435_0 := by decide +kernel
def adaptiveNumericSpans1435_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 5401698485408696820774490141234022030676511569533462665288700151053406621350135949660141421123802057848726999994350370136977383621650382410185844308252659730351220221639003209856
def adaptiveNumericSpans1435_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1435_1Chunk0].flatten
def adaptiveSpanEven1435_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 718 0 adaptiveNumericSpans1435_1)
def adaptiveSpanWhole1435_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1435_1)
theorem adaptiveSpanNumericCheck1435_1 : coreNumericSpansCheck 1400 6 240 385 adaptiveNumericSpans1435_1 adaptiveRows1435 = true := by decide +kernel
theorem adaptiveSpanEvenCache1435_1 : adaptiveSpanEven1435_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1435_1 : adaptiveSpanEven1435_1.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1435_1 : adaptiveSpanEven1435_1.spans = coreEvenSpans 718 0 adaptiveNumericSpans1435_1 := by decide +kernel
theorem adaptiveSpanWholeCache1435_1 : adaptiveSpanWhole1435_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1435_1 : adaptiveSpanWhole1435_1.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1435_1 : adaptiveSpanWhole1435_1.spans = coreWholeSpans 0 adaptiveNumericSpans1435_1 := by decide +kernel
def adaptiveNumericSpans1435_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 5401698485408696820774490141234022030676511569533462665288700151053406621350135949660141421168483462749326474393148388542509759764880991165426182042039218233431640328241982472320
def adaptiveNumericSpans1435_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1435_2Chunk0].flatten
def adaptiveSpanEven1435_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 718 0 adaptiveNumericSpans1435_2)
def adaptiveSpanWhole1435_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1435_2)
theorem adaptiveSpanNumericCheck1435_2 : coreNumericSpansCheck 1400 6 720 1001 adaptiveNumericSpans1435_2 adaptiveRows1435 = true := by decide +kernel
theorem adaptiveSpanEvenCache1435_2 : adaptiveSpanEven1435_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1435_2 : adaptiveSpanEven1435_2.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1435_2 : adaptiveSpanEven1435_2.spans = coreEvenSpans 718 0 adaptiveNumericSpans1435_2 := by decide +kernel
theorem adaptiveSpanWholeCache1435_2 : adaptiveSpanWhole1435_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1435_2 : adaptiveSpanWhole1435_2.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1435_2 : adaptiveSpanWhole1435_2.spans = coreWholeSpans 0 adaptiveNumericSpans1435_2 := by decide +kernel
def adaptiveNumericSpans1435_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 17681869088823642911195542542138099781385918321231912576871751213435905068654743715750682961553566663656563250649559943668691564980850029148177296984073031937511695217916707695385923542504628342851842615625817416233890269086863126021519375245359218750727561780284850926487750988437374825412718174802230970854425053124027786199104
def adaptiveNumericSpans1435_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1435_3Chunk0].flatten
def adaptiveSpanEven1435_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 718 0 adaptiveNumericSpans1435_3)
def adaptiveSpanWhole1435_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1435_3)
theorem adaptiveSpanNumericCheck1435_3 : coreNumericSpansCheck 1400 6 120 143 adaptiveNumericSpans1435_3 adaptiveRows1435 = true := by decide +kernel
theorem adaptiveSpanEvenCache1435_3 : adaptiveSpanEven1435_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1435_3 : adaptiveSpanEven1435_3.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1435_3 : adaptiveSpanEven1435_3.spans = coreEvenSpans 718 0 adaptiveNumericSpans1435_3 := by decide +kernel
theorem adaptiveSpanWholeCache1435_3 : adaptiveSpanWhole1435_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1435_3 : adaptiveSpanWhole1435_3.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1435_3 : adaptiveSpanWhole1435_3.spans = coreWholeSpans 0 adaptiveNumericSpans1435_3 := by decide +kernel
def adaptiveNumericSpans1435_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 16 57879664205404424615616458048981655665720929061938006077456851386090813811885950230749537550314034605618690516999314187297042330964099454879709691734722486976603942927708848637626464679794176211047846353521570264604300929852404858985015283931123162325648434254146562961181531521324501164984197601505750890108910077290768530768995042510891200533532891712122073452223972427312275880743698518401172083426400834493152042466695107280246137548123143745964285935299847482700061290266688
def adaptiveNumericSpans1435_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1435_4Chunk0].flatten
def adaptiveSpanEven1435_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 718 0 adaptiveNumericSpans1435_4)
def adaptiveSpanWhole1435_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1435_4)
theorem adaptiveSpanNumericCheck1435_4 : coreNumericSpansCheck 1400 6 192 221 adaptiveNumericSpans1435_4 adaptiveRows1435 = true := by decide +kernel
theorem adaptiveSpanEvenCache1435_4 : adaptiveSpanEven1435_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1435_4 : adaptiveSpanEven1435_4.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1435_4 : adaptiveSpanEven1435_4.spans = coreEvenSpans 718 0 adaptiveNumericSpans1435_4 := by decide +kernel
theorem adaptiveSpanWholeCache1435_4 : adaptiveSpanWhole1435_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1435_4 : adaptiveSpanWhole1435_4.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1435_4 : adaptiveSpanWhole1435_4.spans = coreWholeSpans 0 adaptiveNumericSpans1435_4 := by decide +kernel
def adaptiveNumericSpans1435_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 21 189462749198153352689765099696811188434981716019575720724896223392683018096778613051563819737159666760831752680655757688505849343844815622744090857198116989345713969963655677988892818217218261488550990559112991951782590615438542235746449478513068022271971341456594153758909080569465453505270663176682825870768911101172775447921545793045567961501248028599670772011564118615897578192135599779903012927962915649732284532968674890904272119363916861026382188130729590142993747916964177512280941754178900008608483652898769613870149356241174258639586189115701429313781869913457466872760990462848207436292112496362652171652987178824237120
def adaptiveNumericSpans1435_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1435_5Chunk0].flatten
def adaptiveSpanEven1435_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 718 0 adaptiveNumericSpans1435_5)
def adaptiveSpanWhole1435_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1435_5)
theorem adaptiveSpanNumericCheck1435_5 : coreNumericSpansCheck 1400 6 288 323 adaptiveNumericSpans1435_5 adaptiveRows1435 = true := by decide +kernel
theorem adaptiveSpanEvenCache1435_5 : adaptiveSpanEven1435_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1435_5 : adaptiveSpanEven1435_5.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1435_5 : adaptiveSpanEven1435_5.spans = coreEvenSpans 718 0 adaptiveNumericSpans1435_5 := by decide +kernel
theorem adaptiveSpanWholeCache1435_5 : adaptiveSpanWhole1435_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1435_5 : adaptiveSpanWhole1435_5.domainCheck 718 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1435_5 : adaptiveSpanWhole1435_5.spans = coreWholeSpans 0 adaptiveNumericSpans1435_5 := by decide +kernel
end Erdos883Verified
