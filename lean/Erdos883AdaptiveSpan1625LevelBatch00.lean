import Erdos883AdaptiveCertificate1625Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1625_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 15859433507687967701122249213980433715586217814100308910032912726938478252205751900145851958802742267330909816767204512894184924921616440793058554023186170766595586891735682318267340640843296334474249959171890845599051206129287093336562813591228614523744654305156936510815564130166812834989227376704
def adaptiveNumericSpans1625_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1625_0Chunk0].flatten
def adaptiveSpanEven1625_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 813 0 adaptiveNumericSpans1625_0)
def adaptiveSpanWhole1625_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1625_0)
theorem adaptiveSpanNumericCheck1625_0 : coreNumericSpansCheck 1586 6 480 1155 adaptiveNumericSpans1625_0 adaptiveRows1625 = true := by decide +kernel
theorem adaptiveSpanEvenCache1625_0 : adaptiveSpanEven1625_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1625_0 : adaptiveSpanEven1625_0.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1625_0 : adaptiveSpanEven1625_0.spans = coreEvenSpans 813 0 adaptiveNumericSpans1625_0 := by decide +kernel
theorem adaptiveSpanWholeCache1625_0 : adaptiveSpanWhole1625_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1625_0 : adaptiveSpanWhole1625_0.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1625_0 : adaptiveSpanWhole1625_0.spans = coreWholeSpans 0 adaptiveNumericSpans1625_0 := by decide +kernel
def adaptiveNumericSpans1625_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 7 7785544139591480397300583335768931895017831811120122357375452721728580944541455785911437102873221573955328758324560764837989196549836418871521653728820619208763230851931102032490170852652672844922636646482048
def adaptiveNumericSpans1625_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1625_1Chunk0].flatten
def adaptiveSpanEven1625_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 813 0 adaptiveNumericSpans1625_1)
def adaptiveSpanWhole1625_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1625_1)
theorem adaptiveSpanNumericCheck1625_1 : coreNumericSpansCheck 1586 6 240 385 adaptiveNumericSpans1625_1 adaptiveRows1625 = true := by decide +kernel
theorem adaptiveSpanEvenCache1625_1 : adaptiveSpanEven1625_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1625_1 : adaptiveSpanEven1625_1.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1625_1 : adaptiveSpanEven1625_1.spans = coreEvenSpans 813 0 adaptiveNumericSpans1625_1 := by decide +kernel
theorem adaptiveSpanWholeCache1625_1 : adaptiveSpanWhole1625_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1625_1 : adaptiveSpanWhole1625_1.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1625_1 : adaptiveSpanWhole1625_1.spans = coreWholeSpans 0 adaptiveNumericSpans1625_1 := by decide +kernel
def adaptiveNumericSpans1625_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 9869349701656513959831451531448062430271886427506263362902296717902400354162185627018544982631667360570939643107230546693554553176412563899990755716379746918290465352655895870115776232824783726694106699520696713734368761499095470861975680
def adaptiveNumericSpans1625_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1625_2Chunk0].flatten
def adaptiveSpanEven1625_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 813 0 adaptiveNumericSpans1625_2)
def adaptiveSpanWhole1625_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1625_2)
theorem adaptiveSpanNumericCheck1625_2 : coreNumericSpansCheck 1586 6 720 1001 adaptiveNumericSpans1625_2 adaptiveRows1625 = true := by decide +kernel
theorem adaptiveSpanEvenCache1625_2 : adaptiveSpanEven1625_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1625_2 : adaptiveSpanEven1625_2.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1625_2 : adaptiveSpanEven1625_2.spans = coreEvenSpans 813 0 adaptiveNumericSpans1625_2 := by decide +kernel
theorem adaptiveSpanWholeCache1625_2 : adaptiveSpanWhole1625_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1625_2 : adaptiveSpanWhole1625_2.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1625_2 : adaptiveSpanWhole1625_2.spans = coreWholeSpans 0 adaptiveNumericSpans1625_2 := by decide +kernel
def adaptiveNumericSpans1625_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 15859433507687967701122249213980433715586217814100308910032912726938478252205751900145851959068614586752614165164323563008440792727946559130974205191252732995136524686966832169136234066749927721318301350330911465449317270399322898227326054185956918366030485578125627203359457150682784750891731779712
def adaptiveNumericSpans1625_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1625_3Chunk0].flatten
def adaptiveSpanEven1625_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 813 0 adaptiveNumericSpans1625_3)
def adaptiveSpanWhole1625_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1625_3)
theorem adaptiveSpanNumericCheck1625_3 : coreNumericSpansCheck 1586 6 120 143 adaptiveNumericSpans1625_3 adaptiveRows1625 = true := by decide +kernel
theorem adaptiveSpanEvenCache1625_3 : adaptiveSpanEven1625_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1625_3 : adaptiveSpanEven1625_3.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1625_3 : adaptiveSpanEven1625_3.spans = coreEvenSpans 813 0 adaptiveNumericSpans1625_3 := by decide +kernel
theorem adaptiveSpanWholeCache1625_3 : adaptiveSpanWhole1625_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1625_3 : adaptiveSpanWhole1625_3.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1625_3 : adaptiveSpanWhole1625_3.spans = coreWholeSpans 0 adaptiveNumericSpans1625_3 := by decide +kernel
def adaptiveNumericSpans1625_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 40953020241754687657185856915868193281701326680489736285440440480788870755613627377160127654572448501577530260089663728130561721321498280054638400472701814026537040761067673257873903909697984322625691929661757546308230823023591983743305724991300528546670292970927341188878684467958980673093676919460434975795822032277991344501934270152460590728161861499266114653677262254020376876123992669010673078124006196858872397888
def adaptiveNumericSpans1625_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1625_4Chunk0].flatten
def adaptiveSpanEven1625_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 813 0 adaptiveNumericSpans1625_4)
def adaptiveSpanWhole1625_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1625_4)
theorem adaptiveSpanNumericCheck1625_4 : coreNumericSpansCheck 1586 6 192 221 adaptiveNumericSpans1625_4 adaptiveRows1625 = true := by decide +kernel
theorem adaptiveSpanEvenCache1625_4 : adaptiveSpanEven1625_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1625_4 : adaptiveSpanEven1625_4.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1625_4 : adaptiveSpanEven1625_4.spans = coreEvenSpans 813 0 adaptiveNumericSpans1625_4 := by decide +kernel
theorem adaptiveSpanWholeCache1625_4 : adaptiveSpanWhole1625_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1625_4 : adaptiveSpanWhole1625_4.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1625_4 : adaptiveSpanWhole1625_4.spans = coreWholeSpans 0 adaptiveNumericSpans1625_4 := by decide +kernel
def adaptiveNumericSpans1625_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 32306236619445022633933232994312720089378249079962965811689787519124988934859996939781089227421612584239093697964507181870778730263706026949370704182254273533996188966395986976787185790019818011038219299537578610674639247916408459650466191348540954896814953386568068578735729520374185861619422924807327087353132939855745207819139050348986856379645293697723030367214054906548796756588494912
def adaptiveNumericSpans1625_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1625_5Chunk0].flatten
def adaptiveSpanEven1625_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 813 0 adaptiveNumericSpans1625_5)
def adaptiveSpanWhole1625_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1625_5)
theorem adaptiveSpanNumericCheck1625_5 : coreNumericSpansCheck 1586 6 288 323 adaptiveNumericSpans1625_5 adaptiveRows1625 = true := by decide +kernel
theorem adaptiveSpanEvenCache1625_5 : adaptiveSpanEven1625_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1625_5 : adaptiveSpanEven1625_5.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1625_5 : adaptiveSpanEven1625_5.spans = coreEvenSpans 813 0 adaptiveNumericSpans1625_5 := by decide +kernel
theorem adaptiveSpanWholeCache1625_5 : adaptiveSpanWhole1625_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1625_5 : adaptiveSpanWhole1625_5.domainCheck 813 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1625_5 : adaptiveSpanWhole1625_5.spans = coreWholeSpans 0 adaptiveNumericSpans1625_5 := by decide +kernel
end Erdos883Verified
