import Erdos883AdaptiveCertificate1751Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1751_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 13494345989357849914497946443310971960622325775202756833109778464903464010150559377741158359493822823758382204216817423158732030904741628491421963061201566636163530256323522964131682126084713501814958391618897114391707743476968113428743430495235917085060720453201428544
def adaptiveNumericSpans1751_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1751_0Chunk0].flatten
def adaptiveSpanEven1751_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 876 0 adaptiveNumericSpans1751_0)
def adaptiveSpanWhole1751_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1751_0)
theorem adaptiveSpanNumericCheck1751_0 : coreNumericSpansCheck 1709 6 480 1155 adaptiveNumericSpans1751_0 adaptiveRows1751 = true := by decide +kernel
theorem adaptiveSpanEvenCache1751_0 : adaptiveSpanEven1751_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1751_0 : adaptiveSpanEven1751_0.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1751_0 : adaptiveSpanEven1751_0.spans = coreEvenSpans 876 0 adaptiveNumericSpans1751_0 := by decide +kernel
theorem adaptiveSpanWholeCache1751_0 : adaptiveSpanWhole1751_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1751_0 : adaptiveSpanWhole1751_0.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1751_0 : adaptiveSpanWhole1751_0.spans = coreWholeSpans 0 adaptiveNumericSpans1751_0 := by decide +kernel
def adaptiveNumericSpans1751_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 7 8397552125651812357986213739741101176411695021543141340606255407229359606000395129807196536024743448510647500419695339623291752836280427512102430529242803250921696918576743996939643608601776233398810271809664
def adaptiveNumericSpans1751_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1751_1Chunk0].flatten
def adaptiveSpanEven1751_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 876 0 adaptiveNumericSpans1751_1)
def adaptiveSpanWhole1751_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1751_1)
theorem adaptiveSpanNumericCheck1751_1 : coreNumericSpansCheck 1709 6 240 385 adaptiveNumericSpans1751_1 adaptiveRows1751 = true := by decide +kernel
theorem adaptiveSpanEvenCache1751_1 : adaptiveSpanEven1751_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1751_1 : adaptiveSpanEven1751_1.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1751_1 : adaptiveSpanEven1751_1.spans = coreEvenSpans 876 0 adaptiveNumericSpans1751_1 := by decide +kernel
theorem adaptiveSpanWholeCache1751_1 : adaptiveSpanWhole1751_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1751_1 : adaptiveSpanWhole1751_1.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1751_1 : adaptiveSpanWhole1751_1.spans = coreWholeSpans 0 adaptiveNumericSpans1751_1 := by decide +kernel
def adaptiveNumericSpans1751_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 7 8397552125651812357986213739741101176411695021543141340606255407229359606000395129807196536024743448510647500419695339623412198365031298976208270097557224769566892476098459283293105931479620826786179116433536
def adaptiveNumericSpans1751_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1751_2Chunk0].flatten
def adaptiveSpanEven1751_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 876 0 adaptiveNumericSpans1751_2)
def adaptiveSpanWhole1751_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1751_2)
theorem adaptiveSpanNumericCheck1751_2 : coreNumericSpansCheck 1709 6 720 1001 adaptiveNumericSpans1751_2 adaptiveRows1751 = true := by decide +kernel
theorem adaptiveSpanEvenCache1751_2 : adaptiveSpanEven1751_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1751_2 : adaptiveSpanEven1751_2.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1751_2 : adaptiveSpanEven1751_2.spans = coreEvenSpans 876 0 adaptiveNumericSpans1751_2 := by decide +kernel
theorem adaptiveSpanWholeCache1751_2 : adaptiveSpanWhole1751_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1751_2 : adaptiveSpanWhole1751_2.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1751_2 : adaptiveSpanWhole1751_2.spans = coreWholeSpans 0 adaptiveNumericSpans1751_2 := by decide +kernel
def adaptiveNumericSpans1751_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 13494345989357849914497946443310971960622325775202756833109778464903464010150559377741158360095330643187844767302389023745882619535921412375102561306362820433945896924039731232206368930555776085632857777952991104994126233715833903443426686313228985955120994462319247488
def adaptiveNumericSpans1751_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1751_3Chunk0].flatten
def adaptiveSpanEven1751_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 876 0 adaptiveNumericSpans1751_3)
def adaptiveSpanWhole1751_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1751_3)
theorem adaptiveSpanNumericCheck1751_3 : coreNumericSpansCheck 1709 6 120 143 adaptiveNumericSpans1751_3 adaptiveRows1751 = true := by decide +kernel
theorem adaptiveSpanEvenCache1751_3 : adaptiveSpanEven1751_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1751_3 : adaptiveSpanEven1751_3.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1751_3 : adaptiveSpanEven1751_3.spans = coreEvenSpans 876 0 adaptiveNumericSpans1751_3 := by decide +kernel
theorem adaptiveSpanWholeCache1751_3 : adaptiveSpanWhole1751_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1751_3 : adaptiveSpanWhole1751_3.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1751_3 : adaptiveSpanWhole1751_3.spans = coreWholeSpans 0 adaptiveNumericSpans1751_3 := by decide +kernel
def adaptiveNumericSpans1751_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 27488468257426924390573444753169046444389357732961973465320240789936084252395602874659617575208050604423104703565401121203373212113184782270474187612219475830260870168643309678807038245875731352440570030325234346967710858184347450304136591154814470713591443861254252426674540251848283717835177322659635455491479815484592972752424372157280892648782514773557376
def adaptiveNumericSpans1751_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1751_4Chunk0].flatten
def adaptiveSpanEven1751_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 876 0 adaptiveNumericSpans1751_4)
def adaptiveSpanWhole1751_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1751_4)
theorem adaptiveSpanNumericCheck1751_4 : coreNumericSpansCheck 1709 6 192 221 adaptiveNumericSpans1751_4 adaptiveRows1751 = true := by decide +kernel
theorem adaptiveSpanEvenCache1751_4 : adaptiveSpanEven1751_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1751_4 : adaptiveSpanEven1751_4.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1751_4 : adaptiveSpanEven1751_4.spans = coreEvenSpans 876 0 adaptiveNumericSpans1751_4 := by decide +kernel
theorem adaptiveSpanWholeCache1751_4 : adaptiveSpanWhole1751_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1751_4 : adaptiveSpanWhole1751_4.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1751_4 : adaptiveSpanWhole1751_4.spans = coreWholeSpans 0 adaptiveNumericSpans1751_4 := by decide +kernel
def adaptiveNumericSpans1751_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 44172265421264956321341461062367082008906492716493191058680875646237021467213797525380239531250280382328115428462792646899240189638643959073014897939139626884096415415448769803262679679082805040001708143155093007159863227061507524103756721639454777342917079178671078866285691296759245778733204761528330214830827337512586474626084123370243201022335158574201642955657327481412024794808149413580011773669035463217095114816
def adaptiveNumericSpans1751_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1751_5Chunk0].flatten
def adaptiveSpanEven1751_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 876 0 adaptiveNumericSpans1751_5)
def adaptiveSpanWhole1751_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1751_5)
theorem adaptiveSpanNumericCheck1751_5 : coreNumericSpansCheck 1709 6 288 323 adaptiveNumericSpans1751_5 adaptiveRows1751 = true := by decide +kernel
theorem adaptiveSpanEvenCache1751_5 : adaptiveSpanEven1751_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1751_5 : adaptiveSpanEven1751_5.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1751_5 : adaptiveSpanEven1751_5.spans = coreEvenSpans 876 0 adaptiveNumericSpans1751_5 := by decide +kernel
theorem adaptiveSpanWholeCache1751_5 : adaptiveSpanWhole1751_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1751_5 : adaptiveSpanWhole1751_5.domainCheck 876 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1751_5 : adaptiveSpanWhole1751_5.spans = coreWholeSpans 0 adaptiveNumericSpans1751_5 := by decide +kernel
end Erdos883Verified
