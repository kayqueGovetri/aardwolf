
import io
import ssl
import copy
import typing
import asyncio
import traceback
from typing import cast
from collections import OrderedDict
import socket
import os
import base64
from datetime import datetime, timedelta
import asn1tools
from PIL import Image
from aardwolf import logger
from aardwolf.keyboard import VK_MODIFIERS
from aardwolf.commons.queuedata.constants import MOUSEBUTTON, VIDEO_FORMAT
from aardwolf.commons.target import RDPTarget
from asyauth.common.credentials import UniCredential
from asyauth.common.constants import asyauthSecret, asyauthProtocol
from aardwolf.commons.cryptolayer import RDPCryptoLayer
from aardwolf.network.x224 import X224Network
from asyauth.common.credentials.credssp import CREDSSPCredential

from aardwolf.protocol.x224.constants import SUPP_PROTOCOLS, NEG_FLAGS
from aardwolf.protocol.x224.server.connectionconfirm import RDP_NEG_RSP

from aardwolf.protocol.pdu.input.keyboard import TS_KEYBOARD_EVENT, KBDFLAGS
from aardwolf.protocol.pdu.input.unicode import TS_UNICODE_KEYBOARD_EVENT
from aardwolf.protocol.pdu.input.mouse import PTRFLAGS, TS_POINTER_EVENT
from aardwolf.protocol.pdu.capabilities import CAPSTYPE
from aardwolf.protocol.pdu.capabilities.general import TS_GENERAL_CAPABILITYSET, OSMAJORTYPE, OSMINORTYPE, EXTRAFLAG
from aardwolf.protocol.pdu.capabilities.bitmap import TS_BITMAP_CAPABILITYSET
from aardwolf.protocol.pdu.capabilities.sound import TS_SOUND_CAPABILITYSET
from aardwolf.protocol.pdu.capabilities.virtualchannel import TS_VIRTUALCHANNEL_CAPABILITYSET, VCCAPS
from aardwolf.protocol.pdu.capabilities.offscreen import TS_OFFSCREEN_CAPABILITYSET
from aardwolf.protocol.pdu.capabilities.glyph import TS_GLYPHCACHE_CAPABILITYSET
from aardwolf.protocol.pdu.capabilities.brush import TS_BRUSH_CAPABILITYSET
from aardwolf.protocol.pdu.capabilities.input import TS_INPUT_CAPABILITYSET, INPUT_FLAG
from aardwolf.protocol.pdu.capabilities.pointer import TS_POINTER_CAPABILITYSET
from aardwolf.protocol.pdu.capabilities.bitmapcache import TS_BITMAPCACHE_CAPABILITYSET
from aardwolf.protocol.pdu.capabilities.order import TS_ORDER_CAPABILITYSET, ORDERFLAG

from aardwolf.protocol.T124.GCCPDU import GCCPDU
from aardwolf.protocol.T124.userdata import TS_UD, TS_SC
from aardwolf.protocol.T124.userdata.constants import TS_UD_TYPE, HIGH_COLOR_DEPTH, ENCRYPTION_FLAG, SUPPORTED_COLOR_DEPTH, \
	COLOR_DEPTH, CONNECTION_TYPE, RNS_UD_CS, ClusterInfo
from aardwolf.protocol.T124.userdata.clientcoredata import TS_UD_CS_CORE
from aardwolf.protocol.T124.userdata.clientsecuritydata import TS_UD_CS_SEC
from aardwolf.protocol.T124.userdata.clientnetworkdata import TS_UD_CS_NET, CHANNEL_DEF
from aardwolf.protocol.T124.userdata.clientclusterdata import TS_UD_CS_CLUSTER
from aardwolf.protocol.T128.security import TS_SECURITY_HEADER,SEC_HDR_FLAG, TS_SECURITY_HEADER1
from aardwolf.protocol.T125.infopacket import TS_INFO_PACKET, INFO_FLAG
from aardwolf.protocol.T125.extendedinfopacket import TS_EXTENDED_INFO_PACKET, TS_TIME_ZONE_INFORMATION, TS_SYSTEMTIME, CLI_AF
from aardwolf.protocol.T125.MCSPDU_ver_2 import MCSPDU_ver_2
from aardwolf.protocol.T128.serverdemandactivepdu import TS_DEMAND_ACTIVE_PDU
from aardwolf.protocol.T128.clientconfirmactivepdu import TS_SHARECONTROLHEADER, TS_CONFIRM_ACTIVE_PDU, TS_CAPS_SET
from aardwolf.protocol.T128.synchronizepdu import TS_SYNCHRONIZE_PDU
from aardwolf.protocol.T128.controlpdu import TS_CONTROL_PDU, CTRLACTION
from aardwolf.protocol.T128.fontlistpdu import TS_FONT_LIST_PDU
from aardwolf.protocol.T128.inputeventpdu import TS_SHAREDATAHEADER, TS_INPUT_EVENT, TS_INPUT_PDU_DATA
from aardwolf.protocol.T125.securityexchangepdu import TS_SECURITY_PACKET
from aardwolf.protocol.T128.seterrorinfopdu import TS_SET_ERROR_INFO_PDU
from aardwolf.protocol.T128.shutdownreqpdu import TS_SHUTDOWN_REQ_PDU
from aardwolf.protocol.T128.share import PDUTYPE, STREAM_TYPE, PDUTYPE2



from aardwolf.protocol.fastpath import TS_FP_UPDATE_PDU, FASTPATH_UPDATETYPE, FASTPATH_FRAGMENT, FASTPATH_SEC, TS_FP_UPDATE
from aardwolf.commons.queuedata import RDPDATATYPE, RDP_KEYBOARD_SCANCODE, RDP_KEYBOARD_UNICODE, RDP_MOUSE, RDP_VIDEO
from aardwolf.channels import MCSChannel
from aardwolf.commons.iosettings import RDPIOSettings

from asysocks.unicomm.client import UniClient
from asysocks.unicomm.common.connection import UniConnection
from aardwolf.network.tpkt import TPKTPacketizer

from aardwolf.network.tpkt import CredSSPPacketizer
from asysocks.unicomm.common.packetizers import Packetizer

class RDPConnection:
	def __init__(self, target:RDPTarget, credentials:UniCredential, iosettings:RDPIOSettings):
		"""RDP client connection object. After successful connection the two asynchronous queues named `ext_out_queue` and `ext_in_queue`
		can be used to communicate with the remote server

		Args:
			target (RDPTarget): Target object specifying the network connection details
			credentials (RDPCredential): Credential object specifying the authentication details
			iosettings (RDPIOSettings): Screen/Keyboard/IO settings
		"""
		self.target = target
		self.credentials = credentials
		self.authapi = None
		self.iosettings = iosettings
		self.disconnected_evt = asyncio.Event() #this will be set if we disconnect for whatever reason

		# these are the main queues with which you can communicate with the server
		# ext_out_queue: yields video,clipboard,bell data
		# ext_in_queue: expects keyboard/mouse/clipboard data
		self.ext_out_queue = asyncio.Queue()
		self.ext_in_queue = asyncio.Queue()

		self.__connection:UniConnection = None
		self._x224net = None
		self.__t125_ber_codec = None
		self._t125_per_codec = None
		self.__t124_codec = None

		self.x224_connection_reply = None
		self.x224_protocol = None

		self.__server_connect_pdu:TS_SC = None # serverconnectpdu message from server (holds security exchange data)
		
		self._initiator = None
		self.__channel_id_lookup = {}
		self.__joined_channels =  OrderedDict({})
		
		for channel in self.iosettings.channels:
			self.__joined_channels[channel.name] = channel(self.iosettings)
		
		self.__channel_task = {} #name -> channeltask

		
		self.__external_reader_task = None
		self.__x224_reader_task = None
		self.client_x224_flags = 0
		self.client_x224_supported_protocols = self.iosettings.supported_protocols 
		self.cryptolayer:RDPCryptoLayer = None
		self.__desktop_buffer = None
		self.desktop_buffer_has_data = False
		self.__terminate_called = False

		self.__vk_to_sc = {
			'VK_BACK'     : 14,
			'VK_ESCAPE'   : 1,
			'VK_TAB'      : 15,
			'VK_RETURN'   : 28,
			'VK_INSERT'   : 82,
			'VK_DELETE'   : 83,
			'VK_HOME'     : 71,
			'VK_END'      : 79,
			'VK_PRIOR'    : 73,
			'VK_NEXT'     : 81,
			'VK_LEFT'     : 75,
			'VK_UP'       : 72,
			'VK_RIGHT'    : 77,
			'VK_DOWN'     : 80,
			'VK_F1'       : 59,
			'VK_F2'       : 60,
			'VK_F3'       : 61,
			'VK_F4'       : 62,
			'VK_F5'       : 63,
			'VK_F6'       : 64,
			'VK_F7'       : 65,
			'VK_F8'       : 66,
			'VK_F9'       : 67,
			'VK_F10'      : 68,
			'VK_F11'      : 87,
			'VK_F12'      : 88,
			'VK_LSHIFT'   : 42,
			'VK_RSHIFT'   : 54,
			'VK_LCONTROL' : 29,
			'VK_LWIN'     : 57435,
			'VK_RWIN'     : 57436,
			'VK_LMENU'    : 56,
			'VK_SCROLL'   : 70,
			'VK_NUMLOCK'  : 69,
			'VK_CAPITAL'  : 58,
			'VK_RCONTROL' : 57629,
			'VK_MULTIPLY' : 55,
			'VK_ADD'      : 78,
			'VK_SUBTRACT' : 74,
			'VK_DIVIDE'   : 57397,
			'VK_SNAPSHOT' : 84,
			#'VK_RCONTROL' : 57373,
			#'VK_PAUSE'    : 57629,
			'VK_RMENU'    : 57400,
			#'VK_DBE_NOCODEINPUT': 98, # except on KLID: 00000412 (ko)
			#'VK_DECIMAL' not found anywhere?
		}

	
	async def terminate(self):
		"""sends a shutdown request to the server and terminates the connection"""
		try:
			if self.__terminate_called is True:
				return True, None
			self.__terminate_called = True

			will_shutdown, err = await self.send_disconnect()
			if err is not None:
				logger.warning('Error while requesting shutdown')
			else:
				if will_shutdown is False:
					logger.warning('Server refused to shutdown, proceeding with termination anyway...')

			for name in self.__joined_channels:
				await self.__joined_channels[name].disconnect()
			
			if self.ext_out_queue is not None:
				# signaling termination via ext_out_queue
				await self.ext_out_queue.put(None)			
			
			if self.__external_reader_task is not None:
				self.__external_reader_task.cancel()
			
			if self.__x224_reader_task is not None:
				self.__x224_reader_task.cancel()
			
			return True, None
		except Exception as e:
			logger.error(f"Error: {e}, {traceback.format_exc()}")
			return None, e
		finally:
			self.disconnected_evt.set()
			if self.__connection is not None:
				await self.__connection.close()
	
	async def __aenter__(self):
		return self
		
	async def __aexit__(self, exc_type, exc, traceback):
		await asyncio.wait_for(self.terminate(), timeout = 5)
	
	async def connect(self):
		"""Initiates the connection to the server, performs authentication, protocol negotiation, and sets up channels.
		Returns:
			Tuple[bool, Exception]: True if connection succeeds, else the exception encountered.
		"""
		try:
			# Inicializa o TPKT e a conexão TCP
			packetizer = TPKTPacketizer()
			client = UniClient(self.target, packetizer)
			self.__connection = await client.connect()
			logger.debug("TCP connection established with %s", self.target)
			logger.debug("Connection object: %s", self.__connection)

			# X224 para negociação inicial
			self._x224net = X224Network(self.__connection)
			logger.debug("X224 network initialized")

			# # Definir protocolos e flags de acordo com as credenciais e tipo de autenticação
			# if self.client_x224_supported_protocols is None and self.credentials is not None:
			# 	if self.credentials.protocol in [asyauthProtocol.NTLM, asyauthProtocol.KERBEROS]:
			# 		if self.credentials.secret and self.credentials.stype not in [
			# 			asyauthSecret.PASSWORD, asyauthSecret.PWPROMPT, asyauthSecret.PWHEX, asyauthSecret.PWB64
			# 		]:
			# 			self.client_x224_flags = 0
			# 			self.client_x224_supported_protocols = SUPP_PROTOCOLS.RDP | SUPP_PROTOCOLS.SSL | SUPP_PROTOCOLS.HYBRID
			# 			logger.debug("Restricted Admin Mode required for non-password secret")
			# 		else:
			# 			self.client_x224_flags = 0
			# 			self.client_x224_supported_protocols = SUPP_PROTOCOLS.RDP | SUPP_PROTOCOLS.SSL | SUPP_PROTOCOLS.HYBRID_EX | SUPP_PROTOCOLS.HYBRID
			# 	elif self.credentials.stype == asyauthSecret.NONE:
			# 		self.client_x224_flags = 0
			# 		self.client_x224_supported_protocols = SUPP_PROTOCOLS.RDP | SUPP_PROTOCOLS.SSL
			# 	else:
			# 		self.client_x224_flags = 0
			# 		self.client_x224_supported_protocols = SUPP_PROTOCOLS.RDP | SUPP_PROTOCOLS.SSL

			self.client_x224_flags = 0
			self.client_x224_supported_protocols = SUPP_PROTOCOLS.RDP
			# Negociação com o servidor
			connection_reply, err = await self._x224net.client_negotiate(
				self.client_x224_flags, self.client_x224_supported_protocols
			)
			if err:
				logger.error("Error during X224 negotiation: %s", err)
				raise err

			logger.debug("Raw X224 negotiation reply: %s", connection_reply)

			# Verificar qual protocolo foi selecionado pelo servidor
			if connection_reply.rdpNegData:
				self.x224_connection_reply = typing.cast(RDP_NEG_RSP, connection_reply.rdpNegData)
				self.x224_protocol = self.x224_connection_reply.selectedProtocol
				self.x224_flag = self.x224_connection_reply.flags
				logger.debug("Server selected protocol: %s, flags: %s", self.x224_protocol, self.x224_flag)
				logger.debug("Server RDP_NEG_RSP detail: %s", self.x224_connection_reply.__dict__)

				# Configurar SSL se necessário
				# if self.x224_protocol & (SUPP_PROTOCOLS.SSL | SUPP_PROTOCOLS.HYBRID | SUPP_PROTOCOLS.HYBRID_EX):
				# ssl_ctx = None
				# if self.target.unsafe_ssl:
				# ssl_ctx = ssl.create_default_context()
				# ssl_ctx.check_hostname = False
				# ssl_ctx.verify_mode = ssl.CERT_NONE
				# ssl_ctx.set_ciphers("ALL:@SECLEVEL=0")
				# logger.warning("Unsafe SSL enabled, skipping certificate verification")
				# await self.__connection.wrap_ssl(ssl_ctx=ssl_ctx)
				# logger.debug("SSL wrapped over TCP connection")

				# CredSSP se HYBRID/HYBRID_EX
				# if self.x224_protocol & (SUPP_PROTOCOLS.HYBRID | SUPP_PROTOCOLS.HYBRID_EX):
				# 	logger.debug("Starting CredSSP authentication...")
				# 	_, err = await self.credssp_auth()
				# 	if err:
				# 		logger.error("CredSSP authentication failed: %s", err)
				# 		raise err
				# 	self.__connection.change_packetizer(TPKTPacketizer())
				# 	logger.debug("CredSSP authentication completed")
			else:
				# Protocolo antigo RDP
				self.x224_protocol = SUPP_PROTOCOLS.RDP
				self.x224_flag = None
				logger.debug("Old RDP protocol selected")

			# Compilar codecs ASN.1 para canais e MCS
			self.__t125_ber_codec = asn1tools.compile_string(MCSPDU_ver_2, "ber")
			self._t125_per_codec = asn1tools.compile_string(MCSPDU_ver_2, "per")
			self.__t124_codec = asn1tools.compile_string(GCCPDU, "per")
			logger.debug("ASN.1 codecs compiled successfully")

			# Estabelecer canais MCS e logar cada PDU relevante
			logger.debug("Establish channels...")

			_, err = await self.__establish_channels()
			if err is not None:
				raise err
			logger.debug('Establish channels OK')
			
			_, err = await self.__erect_domain()
			if err is not None:
				raise err
			logger.debug('Erect domain OK')
			
			_, err = await self.__attach_user()
			if err is not None:
				raise err
			logger.debug('Attach user OK')
			
			_, err = await self.__join_channels()
			if err is not None:
				raise err
			logger.debug('Join channels OK')
			
			if self.x224_protocol == SUPP_PROTOCOLS.RDP:
				# key exchange here because we use old version of the protocol
				_, err = await self.__security_exchange()
				if err is not None:
					raise err
				logger.debug('Security exchange OK')

			_, err = await self.__send_userdata()
			if err is not None:
				raise err
			logger.debug('Send userdata OK')

			_, err = await self.__handle_license()
			if err is not None:
				raise err
			logger.debug('handle license OK')

			_, err = await self.__handle_mandatory_capability_exchange()
			if err is not None:
				raise err
			logger.debug('mandatory capability exchange OK')

			self.__external_reader_task = asyncio.create_task(self.__external_reader())
			logger.debug('RDP connection sequence done')
			self.__desktop_buffer = Image.new(mode="RGBA", size=(self.iosettings.video_width, self.iosettings.video_height))
			return True, None
		except Exception as e:
			self.disconnected_evt.set()
			return None, e
	
	def get_extra_info(self):
		# for NTLM fingerprinting
		ntlm_data = self.authapi.get_extra_info()
		if ntlm_data is not None:
			return ntlm_data.to_dict()
		return None
		 
	
	async def credssp_auth(self):
		try:
			#constructing authentication API is not specified
			if self.authapi is None:
				if self.credentials is None:
					raise Exception('No auth API nor credentials were supplied!')
				
				
				self.authapi = CREDSSPCredential([self.credentials]).build_context()

			self.__connection.change_packetizer(CredSSPPacketizer())

			certificate = self.__connection.get_peer_certificate()

			# credSSP auth happends here
			token = None
			data, to_continue, err = await self.authapi.authenticate(token, flags = None, certificate = certificate, spn=self.target.to_target_string())
			if err is not None:
				raise err

			await self.__connection.write(data)
			
			for _ in range(10):
				token = await self.__connection.read_one()
				data, to_continue, err = await self.authapi.authenticate(token, flags = None, certificate = certificate, spn=self.target.to_target_string())
				if err is not None:
					raise err
				
				if to_continue is False:
					# credSSP auth finished, flushing remaining data
					if data is not None:
						await self.__connection.write(data)
					
					# if HYBRID_EX auth was selected by the server, the server MUST send
					# an extra packet informing us if the credSSP auth was successful or not
					if SUPP_PROTOCOLS.HYBRID_EX in self.x224_protocol:
						self.__connection.change_packetizer(Packetizer())
						authresult_raw = await self.__connection.read_one()
						authresult = int.from_bytes(authresult_raw, byteorder='little', signed=False)
						#print('Early User Authorization Result PDU %s' % authresult)
						if authresult == 5:
							raise Exception('Authentication failed! (early user auth)')
					return True, None
				
				await self.__connection.write(data)

		except Exception as e:
			return None, e

	async def __establish_channels(self):
		"""Establishes MCS channels, encodes user data, and performs initial MCS Connect sequence."""
		try:
			ts_ud = TS_UD()

			# ---------- CS_CORE ----------
			ud_core = TS_UD_CS_CORE()
			ud_core.desktopWidth = self.iosettings.video_width
			ud_core.desktopHeight = self.iosettings.video_height

			# Configura color depth mínimo
			color_depth_map = {
				4: COLOR_DEPTH.COLOR_4BPP,
				8: COLOR_DEPTH.COLOR_8BPP,
				15: COLOR_DEPTH.COLOR_16BPP_555,
				16: COLOR_DEPTH.COLOR_16BPP_565,
				24: COLOR_DEPTH.COLOR_24BPP
			}
			ud_core.colorDepth = color_depth_map.get(self.iosettings.video_bpp_min, COLOR_DEPTH.COLOR_8BPP)
			ud_core.postBeta2ColorDepth = color_depth_map.get(self.iosettings.video_bpp_min, COLOR_DEPTH.COLOR_8BPP)

			# Keyboard and client info
			ud_core.keyboardLayout = self.iosettings.keyboard_layout
			ud_core.clientBuild = 2600
			ud_core.clientName = "mstsc"
			ud_core.imeFileName = ""
			ud_core.clientProductId = 1
			ud_core.serialNumber = 0
			ud_core.keyboardLayout = self.iosettings.keyboard_layout
			ud_core.highColorDepth = HIGH_COLOR_DEPTH.HIGH_COLOR_16BPP

			# High color depth máximo
			high_color_map = {
				4: HIGH_COLOR_DEPTH.HIGH_COLOR_4BPP,
				8: HIGH_COLOR_DEPTH.HIGH_COLOR_8BPP,
				15: HIGH_COLOR_DEPTH.HIGH_COLOR_15BPP,
				16: HIGH_COLOR_DEPTH.HIGH_COLOR_16BPP,
				24: HIGH_COLOR_DEPTH.HIGH_COLOR_24BPP
			}
			ud_core.highColorDepth = high_color_map.get(self.iosettings.video_bpp_max, HIGH_COLOR_DEPTH.HIGH_COLOR_16BPP)

			# Suporte a múltiplos color depths
			self.iosettings.video_bpp_supported = [self.iosettings.video_bpp_min, self.iosettings.video_bpp_max]
			ud_core.supportedColorDepths = 0
			supported_color_flag_map = {
				15: SUPPORTED_COLOR_DEPTH.RNS_UD_15BPP_SUPPORT,
				16: SUPPORTED_COLOR_DEPTH.RNS_UD_16BPP_SUPPORT,
				24: SUPPORTED_COLOR_DEPTH.RNS_UD_24BPP_SUPPORT,
				32: SUPPORTED_COLOR_DEPTH.RNS_UD_32BPP_SUPPORT
			}
			for bpp in self.iosettings.video_bpp_supported:
				ud_core.supportedColorDepths |= supported_color_flag_map.get(bpp, 0)

			ud_core.earlyCapabilityFlags = RNS_UD_CS.SUPPORT_ERRINFO_PDU
			ud_core.clientDigProductId = b"\x00" * 64
			ud_core.connectionType = CONNECTION_TYPE.UNK
			ud_core.pad1octet = b"\x00"
			ud_core.serverSelectedProtocol = self.x224_protocol

			# ---------- CS_SECURITY ----------
			ud_sec = TS_UD_CS_SEC()
			if self.x224_protocol != SUPP_PROTOCOLS.RDP:
				ud_sec.encryptionMethods = ENCRYPTION_FLAG.FRENCH
			else:
				ud_sec.encryptionMethods = ENCRYPTION_FLAG.BIT_128
			ud_sec.extEncryptionMethods = ENCRYPTION_FLAG.FRENCH

			# ---------- CS_CLUSTER ----------
			ud_clust = TS_UD_CS_CLUSTER()
			ud_clust.RedirectedSessionID = 0
			ud_clust.Flags = 8 | 4 | ClusterInfo.REDIRECTION_SUPPORTED

			# ---------- CS_NET ----------
			ud_net = TS_UD_CS_NET()
			default_channels = ["rdpdr", "cliprdr", "rdpsnd"]
			for name in default_channels:
				if name not in self.__joined_channels:
					self.__joined_channels[name] = MCSChannel()
				cd = CHANNEL_DEF()
				cd.name = name
				cd.options = self.__joined_channels[name].options if hasattr(self.__joined_channels[name], 'options') else 0
				ud_net.channelDefArray.append(cd)
			
			# Adiciona MCS próprio
			self.__joined_channels["MCS"] = MCSChannel()
			cd_mcs = CHANNEL_DEF()
			cd_mcs.name = "MCS"
			cd_mcs.options = 0
			ud_net.channelDefArray.append(cd_mcs)

			ts_ud.userdata = {
				TS_UD_TYPE.CS_CORE: ud_core,
				TS_UD_TYPE.CS_SECURITY: ud_sec,
				TS_UD_TYPE.CS_CLUSTER: ud_clust,
				TS_UD_TYPE.CS_NET: ud_net
			}

			# Empacotamento T124
			userdata_wrapped = {
				"conferenceName": {"numeric": "0"},
				"lockedConference": False,
				"listedConference": False,
				"conductibleConference": False,
				"terminationMethod": "automatic",
				"userData": [{"key": ("h221NonStandard", b"Duca"), "value": ts_ud.to_bytes()}]
			}
			connect_gcc_pdu = self.__t124_codec.encode("ConnectGCCPDU", ("conferenceCreateRequest", userdata_wrapped))
			t124_wrapper = self.__t124_codec.encode(
				"ConnectData",
				{"t124Identifier": ("object", "0.0.20.124.0.1"), "connectPDU": connect_gcc_pdu},
			)

			# Connect MCS PDU
			initial_connect = {
				"callingDomainSelector": b"\x01",
				"calledDomainSelector": b"\x01",
				"upwardFlag": True,
				"targetParameters": {"maxChannelIds": 34, "maxUserIds": 2, "maxTokenIds": 0, "numPriorities": 1, "minThroughput": 0, "maxHeight": 1, "maxMCSPDUsize": -1, "protocolVersion": 2},
				"minimumParameters": {"maxChannelIds": 1, "maxUserIds": 1, "maxTokenIds": 1, "numPriorities": 1, "minThroughput": 0, "maxHeight": 1, "maxMCSPDUsize": 1056, "protocolVersion": 2},
				"maximumParameters": {"maxChannelIds": -1, "maxUserIds": -1001, "maxTokenIds": -1, "numPriorities": 1, "minThroughput": 0, "maxHeight": 1, "maxMCSPDUsize": -1, "protocolVersion": 2},
				"userData": t124_wrapper,
			}

			conf_create_req = self.__t125_ber_codec.encode("ConnectMCSPDU", ("connect-initial", initial_connect))
			await self._x224net.write(bytes(conf_create_req))
			logger.debug("Initial MCS Connect sent")

			# Leitura da resposta
			response_raw = await self._x224net.read()
			if not response_raw:
				raise ConnectionError("Connection closed by server during MCS connect")

			server_res_raw = response_raw.data
			server_res_t125 = self.__t125_ber_codec.decode("ConnectMCSPDU", server_res_raw)
			if server_res_t125[0] != "connect-response" or server_res_t125[1]["result"] != "rt-successful":
				raise ConnectionError(f"Unexpected MCS response: {server_res_t125}")

			server_res_t124 = self.__t124_codec.decode("ConnectData", server_res_t125[1]["userData"])
			if server_res_t124["t124Identifier"][1] != "0.0.20.124.0.1":
				raise ValueError(f"Unexpected T124 response: {server_res_t124}")

			# Decodifica final do server connect PDU
			data = server_res_t124["connectPDU"]
			m = server_res_raw.find(data)
			remdata = server_res_raw[m + len(data) :]
			server_connect_pdu_raw = self.__t124_codec.decode("ConnectGCCPDU", data + remdata)
			self.__server_connect_pdu = TS_SC.from_bytes(server_connect_pdu_raw[1]["userData"][0]["value"]).serverdata

			logger.debug("Server capability set: %s", self.__server_connect_pdu)

			# Populando canais
			scnet = self.__server_connect_pdu[TS_UD_TYPE.SC_NET]
			for i, name in enumerate(self.__joined_channels):
				self.__joined_channels[name].channel_id = scnet.channelIdArray[i]
				self.__channel_id_lookup[scnet.channelIdArray[i]] = self.__joined_channels[name]

			self.__joined_channels["MCS"] = MCSChannel()
			self.__joined_channels["MCS"].channel_id = scnet.MCSChannelId
			self.__channel_id_lookup[scnet.MCSChannelId] = self.__joined_channels["MCS"]

			return True, None
		except Exception as e:
			logger.error("Error in __establish_channels: %s\n%s", e, traceback.format_exc())
			return None, e


	async def __erect_domain(self):
		"""
		Sends the initial domain establishment request over the X224 network.
		The content is static and cannot be encoded/decoded reliably with the parser,
		so we send it as raw bytes (as per protocol documentation).
		
		Returns:
			Tuple[bool, Exception]: True if successful, else None and the exception.
		"""
		try:
			domain_request_bytes = bytes.fromhex('0400010001')
			await self._x224net.write(domain_request_bytes)
			logger.debug("Erect domain PDU sent: %s", domain_request_bytes.hex())
			return True, None
		except Exception as e:
			logger.error("Error in __erect_domain: %s\n%s", e, traceback.format_exc())
			return None, e
		
	async def __attach_user(self):
		"""
		Sends an Attach User request to the MCS layer and waits for the server confirmation.
		
		Returns:
			Tuple[bool, Exception]: True if successful, else None and the exception.
		"""
		try:
			# Encode the attachUserRequest PDU
			request_pdu = self._t125_per_codec.encode('DomainMCSPDU', ('attachUserRequest', {}))
			await self._x224net.write(request_pdu)
			logger.debug("AttachUserRequest sent")

			# Read server response
			response = await self._x224net.read()
			if response is None:
				raise Exception('Connection closed by server during attach user')

			# Decode response
			response_parsed = self._t125_per_codec.decode('DomainMCSPDU', response.data)
			if response_parsed[0] != 'attachUserConfirm':
				raise Exception(f'Unexpected response type: {response_parsed[0]}')
			if response_parsed[1]['result'] != 'rt-successful':
				raise Exception(f'Server returned error on attach user: {response_parsed[1]["result"]}')

			# Store initiator ID for future requests
			self._initiator = response_parsed[1]['initiator']
			logger.debug("AttachUserConfirm received, initiator: %s", self._initiator)

			return True, None

		except Exception as e:
			logger.error("Error in __attach_user: %s\n%s", e, traceback.format_exc())
			return None, e
	
	async def __join_channels(self):
		"""
		Sends channel join requests for all joined channels and starts the reader tasks.

		Returns:
			Tuple[bool, Exception]: True if all channels joined successfully, else None and the exception.
		"""
		try:
			for name, channel in self.__joined_channels.items():
				# Encode and send the channelJoinRequest PDU
				joindata = self._t125_per_codec.encode(
					'DomainMCSPDU',
					('channelJoinRequest', {'initiator': self._initiator, 'channelId': channel.channel_id})
				)
				await self._x224net.write(bytes(joindata))
				logger.debug("ChannelJoinRequest sent for channel: %s (ID: %s)", name, channel.channel_id)

				# Await server confirmation
				response = await self._x224net.read()
				if response is None:
					raise Exception(f'Connection closed by server while joining channel: {name}')

				# Decode response
				decoded = self._t125_per_codec.decode('DomainMCSPDU', response.data)
				if decoded[0] != 'channelJoinConfirm':
					raise Exception(f'Could not join channel "{name}". Server response: {decoded}')

				logger.debug("Channel joined successfully: %s", name)

				# Start the channel task
				self.__channel_task[name] = asyncio.create_task(channel.run(self))

			# Start the X224 reader task
			self.__x224_reader_task = asyncio.create_task(self.__x224_reader())
			logger.debug("X224 reader task started")

			return True, None

		except Exception as e:
			logger.error("Error in __join_channels: %s\n%s", e, traceback.format_exc())
			return None, e

	async def __security_exchange(self):
		"""
		Performs the RDP security exchange using the server's certificate and client random.
		
		Returns:
			Tuple[bool, Exception]: True if the security exchange succeeded, else None and the exception.
		"""
		try:
			server_security = self.__server_connect_pdu[TS_UD_TYPE.SC_SECURITY]

			# Initialize cryptography layer with server random
			self.cryptolayer = RDPCryptoLayer(server_security.serverRandom)
			logger.debug("Initialized RDPCryptoLayer with server random")

			# Encrypt the client random using the server certificate
			enc_secret = server_security.serverCertificate.encrypt(self.cryptolayer.ClientRandom)
			logger.debug("Encrypted client random using server certificate")

			# Prepare security exchange packet
			secexchange = TS_SECURITY_PACKET()
			secexchange.encryptedClientRandom = enc_secret

			# Prepare security header
			sec_hdr = TS_SECURITY_HEADER()
			sec_hdr.flags = SEC_HDR_FLAG.EXCHANGE_PKT
			sec_hdr.flagsHi = 0

			# Send the packet over MCS channel
			await self.handle_out_data(
				secexchange,
				sec_hdr,
				None,
				None,
				self.__joined_channels['MCS'].channel_id,
				False
			)
			logger.debug("Security exchange packet sent on MCS channel")

			return True, None

		except Exception as e:
			logger.error("Error in __security_exchange: %s\n%s", e, traceback.format_exc())
			return None, e

	async def __send_userdata(self):
		try:
			systime = TS_SYSTEMTIME()
			systime.wYear = 0
			systime.wMonth = 10
			systime.wDayOfWeek = 0
			systime.wDay = 5
			systime.wHour = 3
			systime.wMinute = 0
			systime.wSecond = 0
			systime.wMilliseconds = 0

			systz = TS_TIME_ZONE_INFORMATION()
			systz.Bias = 4294967236
			systz.StandardName = b'G\x00T\x00B\x00,\x00 \x00s\x00o\x00m\x00m\x00a\x00r\x00t\x00i\x00d\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
			systz.StandardDate = systime
			systz.StandardBias = 0
			systz.DaylightName = b'G\x00T\x00B\x00,\x00 \x00s\x00o\x00m\x00m\x00a\x00r\x00t\x00i\x00d\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
			systz.DaylightDate = systime
			systz.DaylightBias = 4294967236

			extinfo = TS_EXTENDED_INFO_PACKET()
			extinfo.clientAddressFamily = CLI_AF.AF_INET
			extinfo.clientAddress = '10.10.10.101'
			extinfo.clientDir = 'C:\\WINNT\\System32\\mstscax.dll'
			extinfo.clientTimeZone = systz
			extinfo.clientSessionId = 0
			if self.iosettings.performance_flags is not None:
				extinfo.performanceFlags = self.iosettings.performance_flags

			info = TS_INFO_PACKET()
			info.CodePage = 0
			info.flags = INFO_FLAG.ENABLEWINDOWSKEY|INFO_FLAG.MAXIMIZESHELL|INFO_FLAG.UNICODE|INFO_FLAG.DISABLECTRLALTDEL|INFO_FLAG.MOUSE
			info.Domain = ''
			info.UserName = ''
			info.Password = ''
			if self.authapi is None or SUPP_PROTOCOLS.SSL in self.x224_protocol:
				if self.credentials.domain is not None:
					info.Domain = self.credentials.domain
				if self.credentials.username is not None:
					info.UserName = self.credentials.username
				if self.credentials.secret is not None:
					info.Password = self.credentials.secret
			info.AlternateShell = '' 
			info.WorkingDir = ''
			info.extrainfo = extinfo

			sec_hdr = TS_SECURITY_HEADER()
			sec_hdr.flags = SEC_HDR_FLAG.INFO_PKT
			if self.cryptolayer is not None:
				sec_hdr.flags |= SEC_HDR_FLAG.ENCRYPT
			sec_hdr.flagsHi = 0

			await self.handle_out_data(info, sec_hdr, None, None, self.__joined_channels['MCS'].channel_id, False)
			return True, None
		except Exception as e:
			return None, e

	async def __send_client_license_blob(self, channel_id):
		"""
		Monta e envia um ClientLicense blob mínimo (clientRandom + HWID).
		Usa self._t125_per_codec.encode('DomainMCSPDU', ('clientLicense', blob))
		e self.handle_out_data para enviar no canal MCS.
		"""
		# Gera clientRandom e HWID (32 bytes cada)
		client_rand = os.urandom(32)
		hwid = os.urandom(32)

		# Monta blob minimal (heurística aceitada por muitos servidores)
		# layout: version(2) | platformId(2) | clientRandom(32) | hwidLen(2) | hwid
		version = 0x0100
		platform_id = 0x0002  # PLATFORM_ID_WIN32NT (típico)
		blob = struct.pack('<H', version)
		blob += struct.pack('<H', platform_id)
		blob += client_rand
		blob += struct.pack('<H', len(hwid))
		blob += hwid

		# Encoda como DomainMCSPDU - ajuste a tupla se seu codec espera outro label
		try:
			domain_wrapper = self._t125_per_codec.encode('DomainMCSPDU', ('clientLicense', blob))
		except Exception:
			# alguns forks/versões usam outro identificador, tente alternativa
			domain_wrapper = self._t125_per_codec.encode('DomainMCSPDU', ('ClientLicense', blob))

		# Prepara share header
		share_hdr = TS_SHARECONTROLHEADER()
		share_hdr.pduType = PDUTYPE.DATAPDU
		# security header se aplicável
		sec_hdr = None
		if hasattr(self, 'cryptolayer') and self.cryptolayer:
			sec_hdr = TS_SECURITY_HEADER()
			sec_hdr.flags = SEC_HDR_FLAG.ENCRYPT

		class _RawPDU:
			def __init__(self, raw):
				self._raw = raw
			def to_bytes(self):
				return self._raw

		rawobj = _RawPDU(domain_wrapper)
		await self.handle_out_data(rawobj, sec_hdr, None, share_hdr, channel_id, False)
		logger.debug("Sent ClientLicense blob (len=%d)", len(domain_wrapper))
		return True
	
	async def __handle_license(self):
		try:
			if self.x224_protocol == SUPP_PROTOCOLS.RDP:
				logger.debug("Plain RDP selected; skipping licensing step")
				return True, None
			# https://docs.microsoft.com/en-us/openspecs/windows_protocols/ms-rdpbcgr/7d941d0d-d482-41c5-b728-538faa3efb31
			data, err = await self.__joined_channels['MCS'].out_queue.get()
			if err is not None:
				raise err
			res = self._t125_per_codec.decode('DomainMCSPDU', data)

			# res esperado como (type, payload)
			try:
				ptype = str(res[0]).lower()
				payload = res[1]
			except Exception:
				logger.debug("License: formato inesperado do decode: %s", type(res))
				return None, Exception("License: formato inesperado do decode")
		
			logger.debug("License: recebido PDU type=%s payload_keys=%s", ptype, (list(payload.keys()) if isinstance(payload, dict) else type(payload)))

			# Caso 1: tokenInhibitConfirm
			if ptype == 'tokeninhibitconfirm':
				if payload.get('result') != 'rt-successful':
					raise Exception('License error! tokenInhibitConfirm:result not successful')
				logger.debug("License: tokenInhibitConfirm bem-sucedido, prosseguindo.")
				return True, None

			# Caso 2: LicenseRequest -> enviar client license blob
			elif ptype in ('licenserequest', 'license_request'):
				logger.debug("License: LicenseRequest recebido; enviando ClientLicense blob")
				try:
					await self.__send_client_license_blob(self.__joined_channels['MCS'].channel_id)
				except Exception as e_send:
					logger.error("License: falha ao enviar client license blob: %s", e_send)
					return None, e_send

			# Caso 3: LicenseError -> assume ValidClient
			elif ptype in ('licenseerror', 'license_error'):
				logger.debug("License: LicenseError recebido; assumindo ValidClient e prosseguindo. payload=%s", payload)
				return True, None

			# Caso 4: tokenInhibit
			elif ptype == 'tokeninhibit':
				logger.debug("License: tokenInhibit recebido; aguardando próxima mensagem de licensing")

			# Qualquer outro PDU
			else:
				logger.debug("License: PDU de outro tipo recebido (%s), ignorando", ptype)

			return True, None
		except Exception as e:
			logger.error(f"Error: {e}, {traceback.format_exc()}")
			return None, e
		
	async def __handle_mandatory_capability_exchange(self):
		"""
		Handles the mandatory RDP capability exchange with the server.
		Adapted for plain RDP (selectedProtocol == 0) to avoid blocking.
		"""
		try:
			SHARE_ID = 0x103EA
			channel_id = self.__joined_channels['MCS'].channel_id
			server_caps = {}

			# ---------- Step 1: Receive server capability PDU (with timeout) ----------
			logger.debug("Step 1: Waiting for server capability response...")
			try:
				if self.x224_protocol == SUPP_PROTOCOLS.RDP:
					# Plain RDP: server might not send capabilities
					data, err = await asyncio.wait_for(
						self.__joined_channels['MCS'].out_queue.get(), timeout=3
					)
					if err:
						raise err
					# parse if needed, otherwise ignore
					logger.debug("Step 1: Received capability PDU in plain RDP, ignoring contents")
				else:
					# Encrypted / TLS RDP: decode normally
					data, err = await asyncio.wait_for(
						self.__joined_channels['MCS'].out_queue.get(), timeout=5
					)
					if err:
						raise err
					data_start_offset = 4 if self.__server_connect_pdu[TS_UD_TYPE.SC_SECURITY].encryptionLevel == 1 else 0
					data = data[data_start_offset:]
					shc = TS_SHARECONTROLHEADER.from_bytes(data)
					if shc.pduType == PDUTYPE.DEMANDACTIVEPDU:
						res = TS_DEMAND_ACTIVE_PDU.from_bytes(data)
						for cap_set in res.capabilitySets:
							server_caps[cap_set.capabilitySetType] = cap_set.capability
						logger.debug("Step 1: Extracted server capability sets: %s", list(server_caps.keys()))
					else:
						logger.debug("Step 1: Unexpected PDU: %s, ignoring", shc.pduType.name)
			except asyncio.TimeoutError:
				logger.debug("Step 1: No server capability PDU received; using default capabilities")

			# ---------- Step 2: Build client capabilities ----------
			caps = []

			# GENERAL capability
			general_cap = TS_GENERAL_CAPABILITYSET()
			general_cap.osMajorType = OSMAJORTYPE.WINDOWS
			general_cap.osMinorType = OSMINORTYPE.WINDOWS_NT
			general_cap.extraFlags = EXTRAFLAG.FASTPATH_OUTPUT_SUPPORTED | EXTRAFLAG.NO_BITMAP_COMPRESSION_HDR | EXTRAFLAG.LONG_CREDENTIALS_SUPPORTED
			if self.cryptolayer and getattr(self.cryptolayer, 'use_encrypted_mac', False):
				general_cap.extraFlags |= EXTRAFLAG.ENC_SALTED_CHECKSUM
			caps.append(general_cap)
			logger.debug("Step 2: GENERAL capability set: %s", general_cap.extraFlags)

			# BITMAP capability
			bitmap_cap = TS_BITMAP_CAPABILITYSET()
			bitmap_cap.desktopWidth = self.iosettings.video_width
			bitmap_cap.desktopHeight = self.iosettings.video_height
			bitmap_cap.preferredBitsPerPixel = self.iosettings.video_bpp_max
			caps.append(bitmap_cap)
			logger.debug("Step 2: BITMAP capability set: %dx%d@%dbpp", bitmap_cap.desktopWidth, bitmap_cap.desktopHeight, bitmap_cap.preferredBitsPerPixel)

			# ORDER capability
			order_cap = TS_ORDER_CAPABILITYSET()
			order_cap.orderFlags = ORDERFLAG.ZEROBOUNDSDELTASSUPPORT | ORDERFLAG.NEGOTIATEORDERSUPPORT | ORDERFLAG.SOLIDPATTERNBRUSHONLY
			caps.append(order_cap)

			# INPUT capability
			input_cap = TS_INPUT_CAPABILITYSET()
			input_cap.inputFlags = INPUT_FLAG.SCANCODES
			input_cap.keyboardLayout = self.iosettings.keyboard_layout
			input_cap.keyboardType = self.iosettings.keyboard_type
			input_cap.keyboardSubType = self.iosettings.keyboard_subtype
			input_cap.keyboardFunctionKey = self.iosettings.keyboard_functionkey
			caps.append(input_cap)

			# Add fixed capability sets
			for fixed_cap in (TS_BITMAPCACHE_CAPABILITYSET, TS_POINTER_CAPABILITYSET, TS_BRUSH_CAPABILITYSET,
							TS_GLYPHCACHE_CAPABILITYSET, TS_OFFSCREEN_CAPABILITYSET, TS_VIRTUALCHANNEL_CAPABILITYSET,
							TS_SOUND_CAPABILITYSET):
				caps.append(fixed_cap())

			# ---------- Step 3: Send CONFIRM_ACTIVE ----------
			share_hdr = TS_SHARECONTROLHEADER()
			share_hdr.pduType = PDUTYPE.CONFIRMACTIVEPDU
			share_hdr.pduVersion = 1
			share_hdr.pduSource = channel_id

			msg = TS_CONFIRM_ACTIVE_PDU()
			msg.shareID = SHARE_ID
			msg.originatorID = 1002
			for c in caps:
				msg.capabilitySets.append(TS_CAPS_SET.from_capability(c))

			await self.handle_out_data(msg, None, None, share_hdr, channel_id, False)
			logger.debug("Step 3: CONFIRM_ACTIVE sent successfully")

			# ---------- Step 4: SYNCHRONIZE, CONTROL, FONTLIST ----------
			data_hdr = TS_SHAREDATAHEADER()
			data_hdr.shareID = SHARE_ID
			data_hdr.streamID = STREAM_TYPE.MED

			# SYNCHRONIZE
			data_hdr.pduType2 = PDUTYPE2.SYNCHRONIZE
			cli_sync = TS_SYNCHRONIZE_PDU()
			cli_sync.targetUser = channel_id
			await self.handle_out_data(cli_sync, None, data_hdr, None, channel_id, False)

			# CONTROL
			data_hdr.pduType2 = PDUTYPE2.CONTROL
			for action in (CTRLACTION.COOPERATE, CTRLACTION.REQUEST_CONTROL):
				cli_ctrl = TS_CONTROL_PDU()
				cli_ctrl.action = action
				cli_ctrl.grantId = 0
				cli_ctrl.controlId = 0
				await self.handle_out_data(cli_ctrl, None, data_hdr, None, channel_id, False)

			# FONTLIST
			data_hdr.pduType2 = PDUTYPE2.FONTLIST
			cli_font = TS_FONT_LIST_PDU()
			await self.handle_out_data(cli_font, None, data_hdr, None, channel_id, False)

			logger.debug("Step 4: Capability exchange completed successfully")
			return True, None

		except Exception as e:
			logger.error("Exception in __handle_mandatory_capability_exchange: %s\n%s", e, traceback.format_exc())
			return None, e

		async def send_disconnect(self):
			"""Sends a disconnect request to the server. This will NOT close the connection!"""
			try:
				data_start_offset = 0
				if self.__server_connect_pdu[TS_UD_TYPE.SC_SECURITY].encryptionLevel == 1:
					# encryptionLevel == 1 means that server data is not encrypted. This results in this part of the negotiation 
					# that the server sends data to the client with an empty security header (which is not documented....)
					data_start_offset = 4
				
				data_hdr = TS_SHAREDATAHEADER()
				data_hdr.shareID = 0x103EA
				data_hdr.streamID = STREAM_TYPE.MED
				data_hdr.pduType2 = PDUTYPE2.SHUTDOWN_REQUEST
				
				
				cli_input = TS_INPUT_PDU_DATA()
				cli_input.slowPathInputEvents.append(TS_SHUTDOWN_REQ_PDU())

				sec_hdr = None
				if self.cryptolayer is not None:
					sec_hdr = TS_SECURITY_HEADER()
					sec_hdr.flags = SEC_HDR_FLAG.ENCRYPT
					sec_hdr.flagsHi = 0

				await self.handle_out_data(cli_input, sec_hdr, data_hdr, None, self.__joined_channels['MCS'].channel_id, False)
				data, err = await self.__joined_channels['MCS'].out_queue.get()
				if err is not None:
					raise err
				
				server_shutdown_reply = False
				data = data[data_start_offset:]
				shc = TS_SHARECONTROLHEADER.from_bytes(data)
				if shc.pduType == PDUTYPE.DATAPDU:
					shd = TS_SHAREDATAHEADER.from_bytes(data)
					if shd.pduType2 == PDUTYPE2.SHUTDOWN_DENIED:
						# server denied ur request
						server_shutdown_reply = False
					elif shd.pduType2 == PDUTYPE2.CONTROL:
						res_control = TS_CONTROL_PDU.from_bytes(data)
						if res_control.action == CTRLACTION.COOPERATE:
							# server will cooperate
							server_shutdown_reply = True
						else:
							# I dunno what the server is thinking
							server_shutdown_reply = False

					else:
						# I dunno what the server is thinking
						# Maybe we consumed the wrong packet?
						server_shutdown_reply = False
				else:
					raise Exception('Unexpected reply! %s' % shc.pduType.name)

				
				return server_shutdown_reply, None
			except Exception as e:
				return None, e

		async def __x224_reader(self):
			# recieves X224 packets and fastpath packets, performs decryption if necessary then dispatches each packet to 
			# the appropriate channel
			# gets activated when all channel setup is done
			# dont activate it before this!!!!
			
			try:
				self.__connection.packetizer.packetizer_control("X224")
				
				async for is_fastpath, response in self.__connection.read():
					#is_fastpath, response, err = await self._x224net.in_queue.get()
					#if err is not None:
					#	raise err

					if response is None:
						raise Exception('Server terminated the connection!')
					
					if is_fastpath is False:
						x = self._t125_per_codec.decode('DomainMCSPDU', response.data)
						if x[0] != 'sendDataIndication':
							#print('Unknown packet!')
							continue
						
						data = x[1]['userData']
						if data is not None:
							if self.cryptolayer is not None:
								sec_hdr = TS_SECURITY_HEADER1.from_bytes(data)
								if SEC_HDR_FLAG.ENCRYPT in sec_hdr.flags:
									orig_data = data[12:]
									data = self.cryptolayer.client_dec(orig_data)
									if SEC_HDR_FLAG.SECURE_CHECKSUM in sec_hdr.flags:
										mac = self.cryptolayer.calc_salted_mac(data, is_server=True)
									else:
										mac = self.cryptolayer.calc_mac(data)
									if mac != sec_hdr.dataSignature:
										print('ERROR! Signature mismatch! Printing debug data')
										print('Encrypted data: %s' % orig_data)
										print('Decrypted data: %s' % data)
										print('Original MAC  : %s' % sec_hdr.dataSignature)
										print('Calculated MAC: %s' % mac)
						await self.__channel_id_lookup[x[1]['channelId']].process_channel_data(data)
					else:
						#print('fastpath data in -> %s' % len(response))
						fpdu = TS_FP_UPDATE_PDU.from_bytes(response)
						if FASTPATH_SEC.ENCRYPTED in fpdu.flags:
							data = self.cryptolayer.client_dec(fpdu.fpOutputUpdates)
							if FASTPATH_SEC.SECURE_CHECKSUM in fpdu.flags:
								mac = self.cryptolayer.calc_salted_mac(data, is_server=True)
							else:
								mac = self.cryptolayer.calc_mac(data)
							if mac != fpdu.dataSignature:
								print('ERROR! Signature mismatch! Printing debug data')
								print('FASTPATH_SEC  : %s' % fpdu)
								print('Encrypted data: %s' % fpdu.fpOutputUpdates[:100])
								print('Decrypted data: %s' % data[:100])
								print('Original MAC  : %s' % fpdu.dataSignature)
								print('Calculated MAC: %s' % mac)
								raise Exception('Signature mismatch')
							fpdu.fpOutputUpdates = TS_FP_UPDATE.from_bytes(data)
						await self.__process_fastpath(fpdu)
			
			except asyncio.CancelledError:
				return None, None
			except Exception as e:
				logger.error(f"Error: {e}, {traceback.format_exc()}")
				return None, e
			finally:
				await self.terminate()

		async def __process_fastpath(self, fpdu):
			# Fastpath was introduced to the RDP specs to speed up data transmission
			# by reducing 4 useless layers from the traffic.
			# Transmission on this channel starts immediately after connection sequence
			# mostly video and channel related info coming in from the server.
			# interesting note: it seems newer servers (>=win2016) only support this protocol of sending
			# high bandwith traffic. If you disable fastpath (during connection sequence) you won't
			# get images at all
			
			try:
				if fpdu.fpOutputUpdates.fragmentation != FASTPATH_FRAGMENT.SINGLE:
					print('WARNING! FRAGMENTATION IS NOT IMPLEMENTED! %s' % fpdu.fpOutputUpdates.fragmentation)
				if fpdu.fpOutputUpdates.updateCode == FASTPATH_UPDATETYPE.BITMAP:
					for bitmapdata in fpdu.fpOutputUpdates.update.rectangles:
						self.desktop_buffer_has_data = True
						res, image = RDP_VIDEO.from_bitmapdata(bitmapdata, self.iosettings.video_out_format)
						self.__desktop_buffer.paste(image, [res.x, res.y, res.x+res.width, res.y+res.height])
						await self.ext_out_queue.put(res)
				#else:
				#	#print(fpdu.fpOutputUpdates.updateCode)
				#	#if fpdu.fpOutputUpdates.updateCode == FASTPATH_UPDATETYPE.CACHED:
				#	#	print(fpdu.fpOutputUpdates)
				#	#if fpdu.fpOutputUpdates.updateCode not in [FASTPATH_UPDATETYPE.CACHED, FASTPATH_UPDATETYPE.POINTER]:
				#	#	print('notbitmap %s' % fpdu.fpOutputUpdates.updateCode.name)
			except Exception as e:
				# the decoder is not perfect yet, so it's better to keep this here...
				logger.error(f"Error: {e}, {traceback.format_exc()}")
				return
		


		async def send_key_virtualkey(self, vk, is_pressed, is_extended, scancode_hint = None, modifiers = VK_MODIFIERS(0)):
			try:
				if vk in self.__vk_to_sc:
					scancode = self.__vk_to_sc[vk]
					is_extended = True
				else:
					scancode = scancode_hint
				return await self.send_key_scancode(scancode, is_pressed, is_extended)
			except Exception as e:
				logger.error(f"Error: {e}, {traceback.format_exc()}")
				return None, e
		
		async def send_key_scancode(self, scancode, is_pressed, is_extended, modifiers = VK_MODIFIERS(0)):
			try:
				data_hdr = TS_SHAREDATAHEADER()
				data_hdr.shareID = 0x103EA
				data_hdr.streamID = STREAM_TYPE.MED
				data_hdr.pduType2 = PDUTYPE2.INPUT
				
				kbi = TS_KEYBOARD_EVENT()
				kbi.keyCode = scancode
				kbi.keyboardFlags = 0
				if is_pressed is False:
					kbi.keyboardFlags |= KBDFLAGS.RELEASE
				if is_extended is True or kbi.keyCode > 57000:
					kbi.keyboardFlags |= KBDFLAGS.EXTENDED
				clii_kb = TS_INPUT_EVENT.from_input(kbi)
				cli_input = TS_INPUT_PDU_DATA()
				cli_input.slowPathInputEvents.append(clii_kb)
				
				sec_hdr = None
				if self.cryptolayer is not None:
					sec_hdr = TS_SECURITY_HEADER()
					sec_hdr.flags = SEC_HDR_FLAG.ENCRYPT
					sec_hdr.flagsHi = 0

				await self.handle_out_data(cli_input, sec_hdr, data_hdr, None, self.__joined_channels['MCS'].channel_id, False)
					

			except Exception as e:
				logger.error(f"Error: {e}, {traceback.format_exc()}")
				return None, e

		async def send_key_char(self, char, is_pressed):
			try:
				data_hdr = TS_SHAREDATAHEADER()
				data_hdr.shareID = 0x103EA
				data_hdr.streamID = STREAM_TYPE.MED
				data_hdr.pduType2 = PDUTYPE2.INPUT
				
				kbi = TS_UNICODE_KEYBOARD_EVENT()
				kbi.unicodeCode = char
				kbi.keyboardFlags = 0
				if is_pressed is False:
					kbi.keyboardFlags |= KBDFLAGS.RELEASE
				clii_kb = TS_INPUT_EVENT.from_input(kbi)
				cli_input = TS_INPUT_PDU_DATA()
				cli_input.slowPathInputEvents.append(clii_kb)

				sec_hdr = None
				if self.cryptolayer is not None:
					sec_hdr = TS_SECURITY_HEADER()
					sec_hdr.flags = SEC_HDR_FLAG.ENCRYPT
					sec_hdr.flagsHi = 0

				await self.handle_out_data(cli_input, sec_hdr, data_hdr, None, self.__joined_channels['MCS'].channel_id, False)
				return True, None

			except Exception as e:
				logger.error(f"Error: {e}, {traceback.format_exc()}")
				return None, e

		async def send_mouse(self, button:MOUSEBUTTON, xPos:int, yPos:int, is_pressed:bool, steps:int = 0):
			try:
				if xPos < 0 or yPos < 0:
					return True, None
				data_hdr = TS_SHAREDATAHEADER()
				data_hdr.shareID = 0x103EA
				data_hdr.streamID = STREAM_TYPE.MED
				data_hdr.pduType2 = PDUTYPE2.INPUT
				
				mouse = TS_POINTER_EVENT()
				mouse.pointerFlags = 0
				if is_pressed is True:
					mouse.pointerFlags |= PTRFLAGS.DOWN
				if button == MOUSEBUTTON.MOUSEBUTTON_LEFT:
					mouse.pointerFlags |= PTRFLAGS.BUTTON1
				if button == MOUSEBUTTON.MOUSEBUTTON_RIGHT:
					mouse.pointerFlags |= PTRFLAGS.BUTTON2
				if button == MOUSEBUTTON.MOUSEBUTTON_MIDDLE:
					mouse.pointerFlags |= PTRFLAGS.BUTTON3
				if button == MOUSEBUTTON.MOUSEBUTTON_HOVER:
					# indicates a simple pointer update with no buttons pressed
					# sending this enables the mouse hover feel on the remote end
					mouse.pointerFlags |= PTRFLAGS.MOVE
				if button == MOUSEBUTTON.MOUSEBUTTON_WHEEL_UP:
					mouse.pointerFlags |= PTRFLAGS.WHEEL
					mouse.pointerFlags |= (PTRFLAGS.WheelRotationMask & steps)

				if button == MOUSEBUTTON.MOUSEBUTTON_WHEEL_DOWN:
					mouse.pointerFlags |= PTRFLAGS.WHEEL_NEGATIVE
					mouse.pointerFlags |= (PTRFLAGS.WheelRotationMask & steps)

				mouse.xPos = xPos
				mouse.yPos = yPos

				clii_mouse = TS_INPUT_EVENT.from_input(mouse)
						
				cli_input = TS_INPUT_PDU_DATA()
				cli_input.slowPathInputEvents.append(clii_mouse)

				sec_hdr = None
				if self.cryptolayer is not None:
					sec_hdr = TS_SECURITY_HEADER()
					sec_hdr.flags = SEC_HDR_FLAG.ENCRYPT
					sec_hdr.flagsHi = 0

						
				await self.handle_out_data(cli_input, sec_hdr, data_hdr, None, self.__joined_channels['MCS'].channel_id, False)
			except Exception as e:
				logger.error(f"Error: {e}, {traceback.format_exc()}")
				return None, e

		def get_desktop_buffer(self, encoding:VIDEO_FORMAT = VIDEO_FORMAT.PIL):
			"""Makes a copy of the current desktop buffer, converts it and returns the object"""
			try:
				image = copy.deepcopy(self.__desktop_buffer)
				if encoding == VIDEO_FORMAT.PIL:
					return image
				elif encoding == VIDEO_FORMAT.RAW:
					return image.tobytes()
				elif encoding == VIDEO_FORMAT.PNG:
					img_byte_arr = io.BytesIO()
					image.save(img_byte_arr, format='PNG')
					return img_byte_arr.getvalue()
				else:
					raise ValueError('Output format of "%s" is not supported!' % encoding)
			except Exception as e:
				logger.error(f"Error: {e}, {traceback.format_exc()}")
				return None, e
		
		async def get_current_clipboard_text(self):
			if self.iosettings.clipboard is not None:
				return await self.iosettings.clipboard.get_current_clipboard_text()
			return None

		async def set_current_clipboard_text(self, text:str):
			if self.iosettings.clipboard is not None:
				await self.iosettings.clipboard.set_current_clipboard_text(text)
		
		async def set_current_clipboard_files(self, filepaths):
			if self.iosettings.clipboard is not None:
				await self.iosettings.clipboard.set_current_clipboard_files(filepaths)

		async def add_vchannel(self, channelname, handler):
			if 'drdynvc' not in self.__joined_channels:
				raise Exception('Dynamic Virtual Channels are not enabled on this connection!')
			if channelname in self.__joined_channels['drdynvc'].defined_channels:
				raise Exception('Channel already defined!')
			self.__joined_channels['drdynvc'].defined_channels[channelname] = handler
		
		def get_vchannels(self):
			if 'drdynvc' not in self.__joined_channels:
				raise Exception('Dynamic Virtual Channels are not enabled on this connection!')
			return self.__joined_channels['drdynvc'].defined_channels
		
		async def __external_reader(self):
			# This coroutine handles keyboard/mouse etc input from the user
			# It wraps the data in it's appropriate format then dispatches it to the server
			try:
				while True:
					indata = await self.ext_in_queue.get()
					if indata is None:
						#signaling exit
						await self.terminate()
						return
					if indata.type == RDPDATATYPE.KEYSCAN:
						indata = cast(RDP_KEYBOARD_SCANCODE, indata)
						#right side control, altgr, and pause buttons still dont work well...
						#if indata.keyCode in [97]:
						#	await self.send_key_virtualkey('VK_RCONTROL', indata.is_pressed, indata.is_extended, scancode_hint=indata.keyCode)
						if indata.vk_code is not None:
							await self.send_key_virtualkey(indata.vk_code, indata.is_pressed, indata.is_extended, scancode_hint=indata.keyCode)
						else:
							await self.send_key_scancode(indata.keyCode, indata.is_pressed, indata.is_extended)
						
					elif indata.type == RDPDATATYPE.KEYUNICODE:
						indata = cast(RDP_KEYBOARD_UNICODE, indata)
						await self.send_key_char(indata.char, indata.is_pressed)

					elif indata.type == RDPDATATYPE.MOUSE:
						indata = cast(RDP_MOUSE, indata)
						await self.send_mouse(indata.button, indata.xPos, indata.yPos, indata.is_pressed)

					elif indata.type == RDPDATATYPE.CLIPBOARD_DATA_TXT:
						if 'cliprdr' not in self.__joined_channels:
							logger.debug('Got clipboard data but no clipboard channel setup!')
							continue
						await self.__joined_channels['cliprdr'].process_user_data(indata)

			except asyncio.CancelledError:
				return None, None

			except Exception as e:
				logger.error(f"Error: {e}, {traceback.format_exc()}")
				await self.terminate()
				return None, e
		
		async def handle_out_data(self, dataobj, sec_hdr, datacontrol_hdr, sharecontrol_hdr, channel_id, is_fastpath):
			try:
				if is_fastpath is False:
					#print('Sending data on channel "%s(%s)"' % (self.name, self.channel_id))
					data = dataobj.to_bytes()
					hdrs = b''
					if sharecontrol_hdr is not None:
						sharecontrol_hdr.pduSource = channel_id
						sharecontrol_hdr.totalLength = len(data) + 6
						hdrs += sharecontrol_hdr.to_bytes()

					elif datacontrol_hdr is not None:
						datacontrol_hdr.shareControlHeader = TS_SHARECONTROLHEADER()
						datacontrol_hdr.shareControlHeader.pduType = PDUTYPE.DATAPDU
						datacontrol_hdr.shareControlHeader.pduSource = channel_id
						datacontrol_hdr.shareControlHeader.totalLength = len(data) + 24
						datacontrol_hdr.uncompressedLength = len(data) + 24 # since there is no compression implemented yet
						datacontrol_hdr.compressedType = 0
						datacontrol_hdr.compressedLength = 0
						hdrs += datacontrol_hdr.to_bytes()
					if sec_hdr is not None:
						sec_hdr = typing.cast(TS_SECURITY_HEADER, sec_hdr)
						if self.x224_protocol == SUPP_PROTOCOLS.RDP:
							userdata = hdrs + data
						else:
							#print('PacketCount: %s' % self.connection.cryptolayer.PacketCount)
							data = hdrs+data
								

							if self.cryptolayer.use_encrypted_mac is True:
								checksum = self.cryptolayer.calc_salted_mac(data)
								sec_hdr.flags |= SEC_HDR_FLAG.SECURE_CHECKSUM
							else:
								checksum = self.cryptolayer.calc_mac(data)
								
							# https://docs.microsoft.com/en-us/openspecs/windows_protocols/ms-rdpbcgr/9791c9e2-e5be-462f-8c23-3404c4af63b3
							enc_data = self.cryptolayer.client_enc(data)
								
							data = checksum + enc_data
							hdrs = sec_hdr.to_bytes()
							userdata = hdrs + data
					else:
						userdata = hdrs + data
					data_wrapper = {
						'initiator': self._initiator,
						'channelId': channel_id,
						'dataPriority': 'high',
						'segmentation': (b'\xc0', 2),
						'userData': userdata
					}
					userdata_wrapped = self._t125_per_codec.encode('DomainMCSPDU', ('sendDataRequest', data_wrapper))
					await self._x224net.write(userdata_wrapped)
					
				else:
					raise NotImplementedError("Fastpath output is not yet implemented")

			except Exception as e:
				logger.error(f"Error: {e}, {traceback.format_exc()}")
				await self.terminate()
				return None, e
			

async def amain():
	try:
		from aardwolf.commons.factory import RDPConnectionFactory
		from aardwolf.commons.iosettings import RDPIOSettings
		from aardwolf.extensions.RDPEDYC.channel import RDPEDYCChannel

		iosettings = RDPIOSettings()
		url = 'rdp+ntlm-password://TEST2\\Administrator:Passw0rd!1@192.168.85.131'
		rdpurl = RDPConnectionFactory.from_url(url, iosettings)
		conn = rdpurl.get_connection(iosettings)
		_, err = await conn.connect()
		if err is not None:
			raise err
		
		while True:
			data = await conn.ext_out_queue.get()
			print(data)
	except Exception as e:
		traceback.print_exc()

	

if __name__ == '__main__':
	asyncio.run(amain())