import Erdos883AdaptiveSpan168405Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength168405_7 : adaptiveNumericSpans168405_7.length = 746 := by decide +kernel
theorem adaptiveSpanEvenCache168405_7 : adaptiveSpanEven168405_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain168405_7 : adaptiveSpanEven168405_7.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanEvenEntries168405_7 : adaptiveSpanEven168405_7.spans = coreEvenSpans 84203 0 adaptiveNumericSpans168405_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache168405_7 : adaptiveSpanWhole168405_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain168405_7 : adaptiveSpanWhole168405_7.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanWholeEntries168405_7 : adaptiveSpanWhole168405_7.spans = coreWholeSpans 0 adaptiveNumericSpans168405_7 := by
  decide +kernel
end Erdos883Verified
