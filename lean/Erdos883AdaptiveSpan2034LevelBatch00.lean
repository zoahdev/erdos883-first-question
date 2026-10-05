import Erdos883AdaptiveCertificate2034Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2034_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 12400278322709074405135661361090999444854115537402982188137089110754554482791873242161126326925992504716643867663850926736512335879966209900239462306101936183241016550484698109359010226385153319127729385085062686006339946553646662520144000
def adaptiveNumericSpans2034_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2034_0Chunk0].flatten
def adaptiveSpanEven2034_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1017 0 adaptiveNumericSpans2034_0)
def adaptiveSpanWhole2034_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2034_0)
theorem adaptiveSpanNumericCheck2034_0 : coreNumericSpansCheck 1985 6 480 1155 adaptiveNumericSpans2034_0 adaptiveRows2034 = true := by decide +kernel
theorem adaptiveSpanEvenCache2034_0 : adaptiveSpanEven2034_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2034_0 : adaptiveSpanEven2034_0.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2034_0 : adaptiveSpanEven2034_0.spans = coreEvenSpans 1017 0 adaptiveNumericSpans2034_0 := by decide +kernel
theorem adaptiveSpanWholeCache2034_0 : adaptiveSpanWhole2034_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2034_0 : adaptiveSpanWhole2034_0.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2034_0 : adaptiveSpanWhole2034_0.spans = coreWholeSpans 0 adaptiveNumericSpans2034_0 := by decide +kernel
def adaptiveNumericSpans2034_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 12400278322709074405135661361090999444854115537402982188137089110754554482791873242161126326925992504716643867663850926736512335879966209900239462306101936183241016550484698109359010275425034010862370146998858813981492621853657176947556480
def adaptiveNumericSpans2034_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2034_1Chunk0].flatten
def adaptiveSpanEven2034_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1017 0 adaptiveNumericSpans2034_1)
def adaptiveSpanWhole2034_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2034_1)
theorem adaptiveSpanNumericCheck2034_1 : coreNumericSpansCheck 1985 6 240 385 adaptiveNumericSpans2034_1 adaptiveRows2034 = true := by decide +kernel
theorem adaptiveSpanEvenCache2034_1 : adaptiveSpanEven2034_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2034_1 : adaptiveSpanEven2034_1.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2034_1 : adaptiveSpanEven2034_1.spans = coreEvenSpans 1017 0 adaptiveNumericSpans2034_1 := by decide +kernel
theorem adaptiveSpanWholeCache2034_1 : adaptiveSpanWhole2034_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2034_1 : adaptiveSpanWhole2034_1.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2034_1 : adaptiveSpanWhole2034_1.spans = coreWholeSpans 0 adaptiveNumericSpans2034_1 := by decide +kernel
def adaptiveNumericSpans2034_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 12400278322709074405135661361090999444854115537402982188137089110754554482791873242161126326925992504716643867663850926736512335879966209900239462306102077998138697945535366417768962590134937112315414498423868115464979398133957936076030080
def adaptiveNumericSpans2034_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2034_2Chunk0].flatten
def adaptiveSpanEven2034_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1017 0 adaptiveNumericSpans2034_2)
def adaptiveSpanWhole2034_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2034_2)
theorem adaptiveSpanNumericCheck2034_2 : coreNumericSpansCheck 1985 6 720 1001 adaptiveNumericSpans2034_2 adaptiveRows2034 = true := by decide +kernel
theorem adaptiveSpanEvenCache2034_2 : adaptiveSpanEven2034_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2034_2 : adaptiveSpanEven2034_2.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2034_2 : adaptiveSpanEven2034_2.spans = coreEvenSpans 1017 0 adaptiveNumericSpans2034_2 := by decide +kernel
theorem adaptiveSpanWholeCache2034_2 : adaptiveSpanWhole2034_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2034_2 : adaptiveSpanWhole2034_2.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2034_2 : adaptiveSpanWhole2034_2.spans = coreWholeSpans 0 adaptiveNumericSpans2034_2 := by decide +kernel
def adaptiveNumericSpans2034_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 19926478996161272305234605932807666998700855085258649158911431590465986211868080901755130648537022160279266852242471901781568006269913412175910260165326811544045296914225460755124644594003240086940162830060743255590209284933310718503146728018324811212516197139048974768598776544957042402718826627200
def adaptiveNumericSpans2034_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2034_3Chunk0].flatten
def adaptiveSpanEven2034_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1017 0 adaptiveNumericSpans2034_3)
def adaptiveSpanWhole2034_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2034_3)
theorem adaptiveSpanNumericCheck2034_3 : coreNumericSpansCheck 1985 6 120 143 adaptiveNumericSpans2034_3 adaptiveRows2034 = true := by decide +kernel
theorem adaptiveSpanEvenCache2034_3 : adaptiveSpanEven2034_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2034_3 : adaptiveSpanEven2034_3.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2034_3 : adaptiveSpanEven2034_3.spans = coreEvenSpans 1017 0 adaptiveNumericSpans2034_3 := by decide +kernel
theorem adaptiveSpanWholeCache2034_3 : adaptiveSpanWhole2034_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2034_3 : adaptiveSpanWhole2034_3.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2034_3 : adaptiveSpanWhole2034_3.spans = coreWholeSpans 0 adaptiveNumericSpans2034_3 := by decide +kernel
def adaptiveNumericSpans2034_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 15 65227149194474049971522705593792130313035674349656226555501790501310395441765474980165723695850848116713143756799363711155570308043795532812194053726188941670085919794802023094812813645158999074195951313979853867743761583004632657692314292773363484509073311269077017674376942487281840268915564916403753758850570743649433816057067314727211239459813356993201907561952606800208117188385514947179938888561636959101068658171592859328098173905993144991872
def adaptiveNumericSpans2034_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans2034_4Chunk0].flatten
def adaptiveSpanEven2034_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 1017 0 adaptiveNumericSpans2034_4)
def adaptiveSpanWhole2034_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2034_4)
theorem adaptiveSpanNumericCheck2034_4 : coreNumericSpansCheck 1985 6 192 221 adaptiveNumericSpans2034_4 adaptiveRows2034 = true := by decide +kernel
theorem adaptiveSpanEvenCache2034_4 : adaptiveSpanEven2034_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2034_4 : adaptiveSpanEven2034_4.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2034_4 : adaptiveSpanEven2034_4.spans = coreEvenSpans 1017 0 adaptiveNumericSpans2034_4 := by decide +kernel
theorem adaptiveSpanWholeCache2034_4 : adaptiveSpanWhole2034_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2034_4 : adaptiveSpanWhole2034_4.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2034_4 : adaptiveSpanWhole2034_4.spans = coreWholeSpans 0 adaptiveNumericSpans2034_4 := by decide +kernel
def adaptiveNumericSpans2034_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 51455147958538790064881512127960900179937226130424553440814252293473334812271875664237054925734308495655925829549495983433526427039433020575165311260187434263761892723297217849892231694790026685989605393100902754402531609138163372679870965373748170734099818265537565290104354698579663770136285603608542302566833129414602318606734950338249251736694086972698436681100511103655511841612749131581139011554328577597895606400
def adaptiveNumericSpans2034_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans2034_5Chunk0].flatten
def adaptiveSpanEven2034_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 1017 0 adaptiveNumericSpans2034_5)
def adaptiveSpanWhole2034_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2034_5)
theorem adaptiveSpanNumericCheck2034_5 : coreNumericSpansCheck 1985 6 288 323 adaptiveNumericSpans2034_5 adaptiveRows2034 = true := by decide +kernel
theorem adaptiveSpanEvenCache2034_5 : adaptiveSpanEven2034_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2034_5 : adaptiveSpanEven2034_5.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2034_5 : adaptiveSpanEven2034_5.spans = coreEvenSpans 1017 0 adaptiveNumericSpans2034_5 := by decide +kernel
theorem adaptiveSpanWholeCache2034_5 : adaptiveSpanWhole2034_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2034_5 : adaptiveSpanWhole2034_5.domainCheck 1017 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2034_5 : adaptiveSpanWhole2034_5.spans = coreWholeSpans 0 adaptiveNumericSpans2034_5 := by decide +kernel
end Erdos883Verified
