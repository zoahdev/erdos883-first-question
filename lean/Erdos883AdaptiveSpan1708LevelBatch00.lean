import Erdos883AdaptiveCertificate1708Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1708_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 13155778165751198745334834982537505235619722762287164416325819231701871902174503811249268867441066657282232420806337607746550625979963837331152073219498273619897606335434696677475361063892845553550279202965758945500814899514957170585356142244161820603725745985182236736
def adaptiveNumericSpans1708_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1708_0Chunk0].flatten
def adaptiveSpanEven1708_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 854 0 adaptiveNumericSpans1708_0)
def adaptiveSpanWhole1708_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1708_0)
theorem adaptiveSpanNumericCheck1708_0 : coreNumericSpansCheck 1667 6 480 1155 adaptiveNumericSpans1708_0 adaptiveRows1708 = true := by decide +kernel
theorem adaptiveSpanEvenCache1708_0 : adaptiveSpanEven1708_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1708_0 : adaptiveSpanEven1708_0.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1708_0 : adaptiveSpanEven1708_0.spans = coreEvenSpans 854 0 adaptiveNumericSpans1708_0 := by decide +kernel
theorem adaptiveSpanWholeCache1708_0 : adaptiveSpanWhole1708_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1708_0 : adaptiveSpanWhole1708_0.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1708_0 : adaptiveSpanWhole1708_0.spans = coreWholeSpans 0 adaptiveNumericSpans1708_0 := by decide +kernel
def adaptiveNumericSpans1708_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 7 8186860851762173724174550153464898632194660747585372103276049182728724714063517070701467412551905177211285813951681466194906514971513689008987100888538197974265480060974602772403168592899864616413461787705472
def adaptiveNumericSpans1708_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1708_1Chunk0].flatten
def adaptiveSpanEven1708_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 854 0 adaptiveNumericSpans1708_1)
def adaptiveSpanWhole1708_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1708_1)
theorem adaptiveSpanNumericCheck1708_1 : coreNumericSpansCheck 1667 6 240 385 adaptiveNumericSpans1708_1 adaptiveRows1708 = true := by decide +kernel
theorem adaptiveSpanEvenCache1708_1 : adaptiveSpanEven1708_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1708_1 : adaptiveSpanEven1708_1.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1708_1 : adaptiveSpanEven1708_1.spans = coreEvenSpans 854 0 adaptiveNumericSpans1708_1 := by decide +kernel
theorem adaptiveSpanWholeCache1708_1 : adaptiveSpanWhole1708_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1708_1 : adaptiveSpanWhole1708_1.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1708_1 : adaptiveSpanWhole1708_1.spans = coreWholeSpans 0 adaptiveNumericSpans1708_1 := by decide +kernel
def adaptiveNumericSpans1708_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 10378079072721312931088573737333728897837355263773440099074773446526923139545066779400353067145398681500246869432408270885723671606263462806629215472090652258134391288404706267040995676529635876842442817918653094196274519936303702795616384
def adaptiveNumericSpans1708_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1708_2Chunk0].flatten
def adaptiveSpanEven1708_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 854 0 adaptiveNumericSpans1708_2)
def adaptiveSpanWhole1708_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1708_2)
theorem adaptiveSpanNumericCheck1708_2 : coreNumericSpansCheck 1667 6 720 1001 adaptiveNumericSpans1708_2 adaptiveRows1708 = true := by decide +kernel
theorem adaptiveSpanEvenCache1708_2 : adaptiveSpanEven1708_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1708_2 : adaptiveSpanEven1708_2.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1708_2 : adaptiveSpanEven1708_2.spans = coreEvenSpans 854 0 adaptiveNumericSpans1708_2 := by decide +kernel
theorem adaptiveSpanWholeCache1708_2 : adaptiveSpanWhole1708_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1708_2 : adaptiveSpanWhole1708_2.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1708_2 : adaptiveSpanWhole1708_2.spans = coreWholeSpans 0 adaptiveNumericSpans1708_2 := by decide +kernel
def adaptiveNumericSpans1708_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 13155778165751198745334834982537505235619722762287164416325819231701871902174503811249268868046531766909730960070213679795226495570359035636264497537210920327036279098872104467398303542492372342778578923293790946000232784867609375863779420367896571865625703947649941632
def adaptiveNumericSpans1708_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1708_3Chunk0].flatten
def adaptiveSpanEven1708_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 854 0 adaptiveNumericSpans1708_3)
def adaptiveSpanWhole1708_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1708_3)
theorem adaptiveSpanNumericCheck1708_3 : coreNumericSpansCheck 1667 6 120 143 adaptiveNumericSpans1708_3 adaptiveRows1708 = true := by decide +kernel
theorem adaptiveSpanEvenCache1708_3 : adaptiveSpanEven1708_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1708_3 : adaptiveSpanEven1708_3.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1708_3 : adaptiveSpanEven1708_3.spans = coreEvenSpans 854 0 adaptiveNumericSpans1708_3 := by decide +kernel
theorem adaptiveSpanWholeCache1708_3 : adaptiveSpanWhole1708_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1708_3 : adaptiveSpanWhole1708_3.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1708_3 : adaptiveSpanWhole1708_3.spans = coreWholeSpans 0 adaptiveNumericSpans1708_3 := by decide +kernel
def adaptiveNumericSpans1708_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 17 87722918684994649003175557417471702506873770745541112488359899917913377394391058012280143419955916220540715454802245948091048476686606102686842748050083534586922003799536333564082151237808766440549888291626332635845945685773446450903614685320528450731749064835777001974413091986171691241959091659277458862644560038852686794497541306644496346812576700226946106866307249492389811489451826420130297444335993517954951382582671533277785307390046886596070809126805319571326751157710285456574587251745663514505642048
def adaptiveNumericSpans1708_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1708_4Chunk0].flatten
def adaptiveSpanEven1708_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 854 0 adaptiveNumericSpans1708_4)
def adaptiveSpanWhole1708_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1708_4)
theorem adaptiveSpanNumericCheck1708_4 : coreNumericSpansCheck 1667 6 192 221 adaptiveNumericSpans1708_4 adaptiveRows1708 = true := by decide +kernel
theorem adaptiveSpanEvenCache1708_4 : adaptiveSpanEven1708_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1708_4 : adaptiveSpanEven1708_4.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1708_4 : adaptiveSpanEven1708_4.spans = coreEvenSpans 854 0 adaptiveNumericSpans1708_4 := by decide +kernel
theorem adaptiveSpanWholeCache1708_4 : adaptiveSpanWhole1708_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1708_4 : adaptiveSpanWhole1708_4.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1708_4 : adaptiveSpanWhole1708_4.spans = coreWholeSpans 0 adaptiveNumericSpans1708_4 := by decide +kernel
def adaptiveNumericSpans1708_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 33971506564649446864706202632358054455575758397814604306641521859576846593213914244933200036553398583086947219712735406757980671600349800467822527387747231463206851535176876257695001880783911587764168421594528403869102181562540607606937789533380695655327123631934199259274176112671678492083169722822417414641138632468052658225789275643499097255280064222926249809622927883924052773475188800
def adaptiveNumericSpans1708_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1708_5Chunk0].flatten
def adaptiveSpanEven1708_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 854 0 adaptiveNumericSpans1708_5)
def adaptiveSpanWhole1708_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1708_5)
theorem adaptiveSpanNumericCheck1708_5 : coreNumericSpansCheck 1667 6 288 323 adaptiveNumericSpans1708_5 adaptiveRows1708 = true := by decide +kernel
theorem adaptiveSpanEvenCache1708_5 : adaptiveSpanEven1708_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1708_5 : adaptiveSpanEven1708_5.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1708_5 : adaptiveSpanEven1708_5.spans = coreEvenSpans 854 0 adaptiveNumericSpans1708_5 := by decide +kernel
theorem adaptiveSpanWholeCache1708_5 : adaptiveSpanWhole1708_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1708_5 : adaptiveSpanWhole1708_5.domainCheck 854 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1708_5 : adaptiveSpanWhole1708_5.spans = coreWholeSpans 0 adaptiveNumericSpans1708_5 := by decide +kernel
end Erdos883Verified
