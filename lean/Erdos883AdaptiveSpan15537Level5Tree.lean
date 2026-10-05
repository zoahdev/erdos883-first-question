import Erdos883AdaptiveSpan15537Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength15537_5 : adaptiveNumericSpans15537_5.length = 402 := by decide +kernel
theorem adaptiveSpanEvenCache15537_5 : adaptiveSpanEven15537_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain15537_5 : adaptiveSpanEven15537_5.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanEvenEntries15537_5 : adaptiveSpanEven15537_5.spans = coreEvenSpans 7769 0 adaptiveNumericSpans15537_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache15537_5 : adaptiveSpanWhole15537_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain15537_5 : adaptiveSpanWhole15537_5.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanWholeEntries15537_5 : adaptiveSpanWhole15537_5.spans = coreWholeSpans 0 adaptiveNumericSpans15537_5 := by
  decide +kernel
end Erdos883Verified
