import Erdos883AdaptiveCertificate1471Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1471_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 11293655139751955500326925390606611776882531100823990077246572280939470947897667665547145234706161055447147666216642504311549277026231149759506265043305937553834950449796135536218567156094695443333258322352200516652339864517146465629216593569433820955710349203858260032
def adaptiveNumericSpans1471_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1471_0Chunk0].flatten
def adaptiveSpanEven1471_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 736 0 adaptiveNumericSpans1471_0)
def adaptiveSpanWhole1471_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1471_0)
theorem adaptiveSpanNumericCheck1471_0 : coreNumericSpansCheck 1436 6 480 1155 adaptiveNumericSpans1471_0 adaptiveRows1471 = true := by decide +kernel
theorem adaptiveSpanEvenCache1471_0 : adaptiveSpanEven1471_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1471_0 : adaptiveSpanEven1471_0.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1471_0 : adaptiveSpanEven1471_0.spans = coreEvenSpans 736 0 adaptiveNumericSpans1471_0 := by decide +kernel
theorem adaptiveSpanWholeCache1471_0 : adaptiveSpanWhole1471_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1471_0 : adaptiveSpanWhole1471_0.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1471_0 : adaptiveSpanWhole1471_0.spans = coreWholeSpans 0 adaptiveNumericSpans1471_0 := by decide +kernel
def adaptiveNumericSpans1471_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 5544160864588240748423641321636606096740612120347097086301916839047500184242683635294364570473818408261358696405948505614007824051748782836983143760029517543691992480903856128128
def adaptiveNumericSpans1471_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1471_1Chunk0].flatten
def adaptiveSpanEven1471_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 736 0 adaptiveNumericSpans1471_1)
def adaptiveSpanWhole1471_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1471_1)
theorem adaptiveSpanNumericCheck1471_1 : coreNumericSpansCheck 1436 6 240 385 adaptiveNumericSpans1471_1 adaptiveRows1471 = true := by decide +kernel
theorem adaptiveSpanEvenCache1471_1 : adaptiveSpanEven1471_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1471_1 : adaptiveSpanEven1471_1.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1471_1 : adaptiveSpanEven1471_1.spans = coreEvenSpans 736 0 adaptiveNumericSpans1471_1 := by decide +kernel
theorem adaptiveSpanWholeCache1471_1 : adaptiveSpanWhole1471_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1471_1 : adaptiveSpanWhole1471_1.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1471_1 : adaptiveSpanWhole1471_1.spans = coreWholeSpans 0 adaptiveNumericSpans1471_1 := by decide +kernel
def adaptiveNumericSpans1471_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 11293655139751955500326925390606611776882531100823990077246572280939470947897667665547145234706161055447147666216642504311040431771381879186816111641649798376724355491573240772712921231490539783666731572966249836136107894660323213527136586870133441542454164683703189568
def adaptiveNumericSpans1471_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1471_2Chunk0].flatten
def adaptiveSpanEven1471_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 736 0 adaptiveNumericSpans1471_2)
def adaptiveSpanWhole1471_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1471_2)
theorem adaptiveSpanNumericCheck1471_2 : coreNumericSpansCheck 1436 6 720 1001 adaptiveNumericSpans1471_2 adaptiveRows1471 = true := by decide +kernel
theorem adaptiveSpanEvenCache1471_2 : adaptiveSpanEven1471_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1471_2 : adaptiveSpanEven1471_2.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1471_2 : adaptiveSpanEven1471_2.spans = coreEvenSpans 736 0 adaptiveNumericSpans1471_2 := by decide +kernel
theorem adaptiveSpanWholeCache1471_2 : adaptiveSpanWhole1471_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1471_2 : adaptiveSpanWhole1471_2.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1471_2 : adaptiveSpanWhole1471_2.spans = coreWholeSpans 0 adaptiveNumericSpans1471_2 := by decide +kernel
def adaptiveNumericSpans1471_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 14316408716677194394418481968301908803578542369388742146956977696035503537933456622778531694456786085261638647366788071242160943395367708619455931445220723681747668825661555919567335392534412975705870653675072611236180172194027813447631776009947689284488417822512913015621500138874300297222671040576
def adaptiveNumericSpans1471_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1471_3Chunk0].flatten
def adaptiveSpanEven1471_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 736 0 adaptiveNumericSpans1471_3)
def adaptiveSpanWhole1471_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1471_3)
theorem adaptiveSpanNumericCheck1471_3 : coreNumericSpansCheck 1436 6 120 143 adaptiveNumericSpans1471_3 adaptiveRows1471 = true := by decide +kernel
theorem adaptiveSpanEvenCache1471_3 : adaptiveSpanEven1471_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1471_3 : adaptiveSpanEven1471_3.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1471_3 : adaptiveSpanEven1471_3.spans = coreEvenSpans 736 0 adaptiveNumericSpans1471_3 := by decide +kernel
theorem adaptiveSpanWholeCache1471_3 : adaptiveSpanWhole1471_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1471_3 : adaptiveSpanWhole1471_3.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1471_3 : adaptiveSpanWhole1471_3.spans = coreWholeSpans 0 adaptiveNumericSpans1471_3 := by decide +kernel
def adaptiveNumericSpans1471_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 36968544663282040680873531628390030780972227025631873364288192887154864534341218665513038368901229795532154079075603888222305794088188613003746452999306299587307174858974094166750824895663885002311961226656081798631544372799836095077604952385874561851147136137008524655875659853149521591288563080064034973353866815808901647714632743108013635142633746004594335725413138178179325692835984269981778327778722322997644886080
def adaptiveNumericSpans1471_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1471_4Chunk0].flatten
def adaptiveSpanEven1471_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 736 0 adaptiveNumericSpans1471_4)
def adaptiveSpanWhole1471_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1471_4)
theorem adaptiveSpanNumericCheck1471_4 : coreNumericSpansCheck 1436 6 192 221 adaptiveNumericSpans1471_4 adaptiveRows1471 = true := by decide +kernel
theorem adaptiveSpanEvenCache1471_4 : adaptiveSpanEven1471_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1471_4 : adaptiveSpanEven1471_4.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1471_4 : adaptiveSpanEven1471_4.spans = coreEvenSpans 736 0 adaptiveNumericSpans1471_4 := by decide +kernel
theorem adaptiveSpanWholeCache1471_4 : adaptiveSpanWhole1471_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1471_4 : adaptiveSpanWhole1471_4.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1471_4 : adaptiveSpanWhole1471_4.spans = coreWholeSpans 0 adaptiveNumericSpans1471_4 := by decide +kernel
def adaptiveNumericSpans1471_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 18 95462019949810484706094413451150935778398832238520103148926997615247412115958662011015280089932903280570652732656079769707231932297285097597060813678860758672089496013016285352718274435688300272221957744120360694787850987715909888952980667799505735282128850814585790883427967440165361954239664930536572698108655763846201446400126302343277650165686773361172561935302815313733285519248102511990849164400702696498178888796234571392057975243362660941069709778552274592723435930042214021113093521913989494101275313509263124990949269647457779776
def adaptiveNumericSpans1471_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1471_5Chunk0].flatten
def adaptiveSpanEven1471_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 736 0 adaptiveNumericSpans1471_5)
def adaptiveSpanWhole1471_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1471_5)
theorem adaptiveSpanNumericCheck1471_5 : coreNumericSpansCheck 1436 6 288 323 adaptiveNumericSpans1471_5 adaptiveRows1471 = true := by decide +kernel
theorem adaptiveSpanEvenCache1471_5 : adaptiveSpanEven1471_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1471_5 : adaptiveSpanEven1471_5.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1471_5 : adaptiveSpanEven1471_5.spans = coreEvenSpans 736 0 adaptiveNumericSpans1471_5 := by decide +kernel
theorem adaptiveSpanWholeCache1471_5 : adaptiveSpanWhole1471_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1471_5 : adaptiveSpanWhole1471_5.domainCheck 736 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1471_5 : adaptiveSpanWhole1471_5.spans = coreWholeSpans 0 adaptiveNumericSpans1471_5 := by decide +kernel
end Erdos883Verified
