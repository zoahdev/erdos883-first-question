import Erdos883AdaptiveSpan15537Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength15537_7 : adaptiveNumericSpans15537_7.length = 402 := by decide +kernel
theorem adaptiveSpanEvenCache15537_7 : adaptiveSpanEven15537_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain15537_7 : adaptiveSpanEven15537_7.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanEvenEntries15537_7 : adaptiveSpanEven15537_7.spans = coreEvenSpans 7769 0 adaptiveNumericSpans15537_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache15537_7 : adaptiveSpanWhole15537_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain15537_7 : adaptiveSpanWhole15537_7.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanWholeEntries15537_7 : adaptiveSpanWhole15537_7.spans = coreWholeSpans 0 adaptiveNumericSpans15537_7 := by
  decide +kernel
end Erdos883Verified
