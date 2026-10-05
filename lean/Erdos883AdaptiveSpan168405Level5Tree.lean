import Erdos883AdaptiveSpan168405Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength168405_5 : adaptiveNumericSpans168405_5.length = 746 := by decide +kernel
theorem adaptiveSpanEvenCache168405_5 : adaptiveSpanEven168405_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain168405_5 : adaptiveSpanEven168405_5.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanEvenEntries168405_5 : adaptiveSpanEven168405_5.spans = coreEvenSpans 84203 0 adaptiveNumericSpans168405_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache168405_5 : adaptiveSpanWhole168405_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain168405_5 : adaptiveSpanWhole168405_5.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanWholeEntries168405_5 : adaptiveSpanWhole168405_5.spans = coreWholeSpans 0 adaptiveNumericSpans168405_5 := by
  decide +kernel
end Erdos883Verified
